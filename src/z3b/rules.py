# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.call import Call
from core.callexplorer import CallExplorer
from itertools import chain
from third_party.memoized import memoized
from z3b.constraints import *
from z3b.model import *
from z3b import enum
from z3b import ordering
from z3b.preconditions import *


rule_order = ordering.Ordering()

# FIXME: Unclear if these are clearer to read or not.
def suit_bids_below_game(lowest_call_name=None):
    all_suit_bids_below_game = (
        '1C', '1D', '1H', '1S',
        '2C', '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
        '4C', '4D'
    )
    lowest_call_index = all_suit_bids_below_game.index(lowest_call_name) if lowest_call_name else 0
    return all_suit_bids_below_game[lowest_call_index:]


def suit_bids_between(low_call_name, high_call_name):
    all_suit_bids = (
        '1C', '1D', '1H', '1S',
        '2C', '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
        '4C', '4D', '4H', '4S',
        '5C', '5D', '5H', '5S',
        '6C', '6D', '6H', '6S',
        '7C', '7D', '7H', '7S',
    )
    low_index = all_suit_bids.index(low_call_name)
    high_index = all_suit_bids.index(high_call_name)
    return all_suit_bids[low_index:high_index]


categories = enum.Enum(
    "Relay",
    "Gadget",
    "NoTrumpSystem",
    "Default",
    "Natural",
    "LawOfTotalTricks",
    "DefaultPass",
)

# This is a public interface from RuleGenerators to the rest of the system.
# This class knows nothing about the DSL.
class CompiledRule(object):
    def __init__(self, rule, preconditions, known_calls, shared_constraints, annotations, constraints, default_priority, conditional_priorities_per_call):
        self.dsl_rule = rule
        self.preconditions = preconditions
        self.known_calls = known_calls
        self.shared_constraints = shared_constraints
        self._annotations = annotations
        self.constraints = constraints
        self.default_priority = default_priority
        self.conditional_priorities_per_call = conditional_priorities_per_call

    def requires_planning(self, history):
        return self.dsl_rule.requires_planning

    def annotations_for_call(self, call):
        if self.dsl_rule.annotations_per_call:
            per_call_annotations = self.dsl_rule.annotations_per_call.get(call.name)
            if per_call_annotations:
                return self._annotations | set(RuleCompiler._ensure_list(per_call_annotations))
        return self._annotations

    @property
    def name(self):
        return self.dsl_rule.name()

    def __str__(self):
        return self.name

    def __repr__(self):
        return "CompiledRule(%s)" % self.dsl_rule.name()

    # FIXME: This exists for compatiblity with KBB's Rule interface and is used by bidder_handler.py
    def explanation_for_bid(self, call):
        return None

    # FIXME: This exists for compatiblity with KBB's Rule interface and is used by bidder_handler.py
    def sayc_page_for_bid(self, call):
        return None

    def _fits_preconditions(self, history, call, expected_call=None):
        try:
            for precondition in self.preconditions:
                if not precondition.fits(history, call):
                    if call == expected_call and expected_call in self.known_calls:
                        print " %s failed: %s" % (self, precondition)
                    return False
        except Exception, e:
            print "Exception evaluating preconditions for %s" % self.name
            raise
        return True

    def calls_over(self, history, expected_call=None):
        for call in history.legal_calls.intersection(self.known_calls):
            if self._fits_preconditions(history, call, expected_call):
                yield self.dsl_rule.category, call

    def _constraint_exprs_for_call(self, history, call):
        exprs = []
        per_call_constraints, _ = self.per_call_constraints_and_priority(call)
        if per_call_constraints:
            exprs.extend(RuleCompiler.exprs_from_constraints(per_call_constraints, history, call))
        exprs.extend(RuleCompiler.exprs_from_constraints(self.shared_constraints, history, call))
        return exprs

    def meaning_of(self, history, call):
        exprs = self._constraint_exprs_for_call(history, call)
        per_call_conditionals = self.conditional_priorities_per_call.get(call.name)
        if per_call_conditionals:
            for condition, priority in per_call_conditionals:
                condition_exprs = RuleCompiler.exprs_from_constraints(condition, history, call)
                yield priority, z3.And(exprs + condition_exprs)

        for condition, priority in self.dsl_rule.conditional_priorities:
            condition_exprs = RuleCompiler.exprs_from_constraints(condition, history, call)
            yield priority, z3.And(exprs + condition_exprs)

        _, priority = self.per_call_constraints_and_priority(call)
        assert priority
        yield priority, z3.And(exprs)

    # constraints accepts various forms including:
    # constraints = { '1H': hearts > 5 }
    # constraints = { '1H': (hearts > 5, priority) }
    # constraints = { ('1H', '2H'): hearts > 5 }

    # FIXME: Should we split this into two methods? on for priority and one for constraints?
    def per_call_constraints_and_priority(self, call):
        constraints_tuple = self.constraints.get(call.name)
        try:
            list(constraints_tuple)
        except TypeError:
            constraints_tuple = (constraints_tuple, self.default_priority)
        assert len(constraints_tuple) == 2
        # FIXME: Is it possible to not end up with a priority anymore?
        assert constraints_tuple[1], "" + self.name + " is missing priority"
        return constraints_tuple


class RuleCompiler(object):
    @classmethod
    def exprs_from_constraints(cls, constraints, history, call):
        if not constraints:
            return [NO_CONSTRAINTS]

        if isinstance(constraints, Constraint):
            return [constraints.expr(history, call)]

        if isinstance(constraints, z3.ExprRef):
            return [constraints]

        return chain.from_iterable([cls.exprs_from_constraints(constraint, history, call) for constraint in constraints])

    @classmethod
    def _collect_from_ancestors(cls, dsl_class, property_name):
        getter = lambda ancestor: getattr(ancestor, property_name, [])
        # The DSL expects that parent preconditions, etc. apply before child ones.
        return map(getter, reversed(dsl_class.__mro__))

    @classmethod
    def _ensure_list(cls, value_or_list):
        if value_or_list and not hasattr(value_or_list, '__iter__'):
            return [value_or_list]
        return value_or_list

    @classmethod
    def _joined_list_from_ancestors(cls, dsl_class, property_name):
        values_from_ancestors = cls._collect_from_ancestors(dsl_class, property_name)
        mapped_values = map(cls._ensure_list, values_from_ancestors)
        return list(chain.from_iterable(mapped_values))

    @classmethod
    def _compile_known_calls(cls, dsl_class, constraints):
        if dsl_class.call_names:
            call_names = cls._ensure_list(dsl_class.call_names)
        else:
            call_names = constraints.keys()
        assert call_names, "%s: call_names or constraints map is required." % dsl_class.__name__
        return map(Call.from_string, call_names)

    @classmethod
    def _flatten_tuple_keyed_dict(cls, original_dict):
        flattened_dict  = {}
        for tuple_key, value in original_dict.iteritems():
            if hasattr(tuple_key, '__iter__'):
                for key in tuple_key:
                    flattened_dict[key] = value
            else:
                flattened_dict[tuple_key] = value
        return flattened_dict

    @classmethod
    def _compile_annotations(cls, dsl_class):
        compiled_set = set(cls._joined_list_from_ancestors(dsl_class, 'annotations'))
        # FIXME: We should probably assert that no more than one of the "implies_artificial"
        # annotations are in this set at once.  Those all have distinct meanings.
        if implies_artificial.intersection(compiled_set):
            compiled_set.add(annotations.Artificial)
        return compiled_set

    @classmethod
    def _validate_rule(cls, dsl_class):
        # Rules have to apply some constraints to the hand.
        assert dsl_class.constraints or dsl_class.shared_constraints, "" + dsl_class.name() + " is missing constraints"
        # conditional_priorities doesn't work with self.constraints
        assert not dsl_class.conditional_priorities or not dsl_class.constraints
        assert not dsl_class.conditional_priorities or dsl_class.call_names
        # FIXME: We should also walk the class and assert that no unexpected properties are found.
        allowed_keys = set([
            "annotations",
            "annotations_per_call",
            "call_names",
            "category",
            "conditional_priorities",
            "constraints",
            "preconditions",
            "priority",
            "requires_planning",
            "shared_constraints",
            "conditional_priorities_per_call",
        ])
        properties = dsl_class.__dict__.keys()
        public_properties = filter(lambda p: not p.startswith("_"), properties)
        unexpected_properties = set(public_properties) - allowed_keys
        assert not unexpected_properties, "%s defines unexpected properties: %s" % (dsl_class, unexpected_properties)

    @classmethod
    def _default_priority(cls, dsl_rule):
        if dsl_rule.priority:
            return dsl_rule.priority
        return dsl_rule # Use the class as the default priority.

    @classmethod
    def compile(cls, dsl_rule):
        cls._validate_rule(dsl_rule)
        constraints = cls._flatten_tuple_keyed_dict(dsl_rule.constraints)
        # Unclear if compiled results should be memoized on the rule?
        return CompiledRule(dsl_rule,
            known_calls=cls._compile_known_calls(dsl_rule, constraints),
            annotations=cls._compile_annotations(dsl_rule),
            preconditions=cls._joined_list_from_ancestors(dsl_rule, 'preconditions'),
            shared_constraints=cls._joined_list_from_ancestors(dsl_rule, 'shared_constraints'),
            constraints=constraints,
            default_priority = cls._default_priority(dsl_rule),
            conditional_priorities_per_call = cls._flatten_tuple_keyed_dict(dsl_rule.conditional_priorities_per_call),
        )


# The rules of SAYC are all described in terms of Rule.
# These classes exist to support the DSL and make it easy to concisely express
# the conventions of SAYC.
class Rule(object):
    # FIXME: Consider splitting call_preconditions out from preconditions
    # for preconditions which only operate on the call?
    preconditions = [] # Auto-collects from parent classes
    category = categories.Default # Intra-bid priority
    requires_planning = False

    # All possible call names must be listed.
    # Having an up-front list makes the bidder's rule-evaluation faster.
    call_names = None # Required.

    constraints = {}
    shared_constraints = [] # Auto-collects from parent classes
    annotations = []
    conditional_priorities = []
    # FIXME: conditional_priorities_per_call is a stepping-stone to allow us to
    # write more conditional priorities and better understand what rules we should
    # develop to generate them.  The syntax is:
    # {'1C': [(condition, priority), (condition, priority)]}
    conditional_priorities_per_call = {}
    annotations_per_call = {}
    priority = None

    def __init__(self):
        assert False, "Rule objects should be compiled into EngineRule objects instead of instantiating them."

    @classmethod
    def name(cls):
        return cls.__name__

    def __repr__(self):
        return "%s()" % self.name


relay_priorities = enum.Enum(
    "SuperAccept",
    "Accept",
)
rule_order.order(*reversed(relay_priorities))


natural_priorities = enum.Enum(
    "SevenLevelNaturalNT",
    "SevenLevelNaturalMajor",
    "SevenLevelNaturalMinor",

    "SixLevelNaturalNT",
    "SixLevelNaturalMajor",
    "SixLevelNaturalMinor",

    "FourLevelNaturalMajor",
    "ThreeLevelNaturalNT", # FIXME: Where does 3N go?
    "FiveLevelNaturalMinor",

    "FourLevelNaturalNT", # Should 4N be higher priority than 5N?
    "FiveLevelNaturalNT",

    "FiveLevelNaturalMajor",

    "FourLevelNaturalMinor",

    "ThreeLevelNaturalMajor",
    "ThreeLevelNaturalMinor",

    "TwoLevelNaturalMajor",
    "TwoLevelNaturalMinor",
    "TwoLevelNaturalNT",

    "OneLevelNaturalNT",
)

# FIXME: Can we order these using a priority compiler?
rule_order.order(*reversed(natural_priorities))

natural_slams = set([
    natural_priorities.SixLevelNaturalMinor,
    natural_priorities.SixLevelNaturalMajor,
    natural_priorities.SixLevelNaturalNT,
    natural_priorities.SevenLevelNaturalMinor,
    natural_priorities.SevenLevelNaturalMajor,
    natural_priorities.SevenLevelNaturalNT,
])

natural_games = set([
    natural_priorities.ThreeLevelNaturalNT,
    natural_priorities.FourLevelNaturalMajor,
    natural_priorities.FourLevelNaturalNT,
    natural_priorities.FiveLevelNaturalMinor,
    natural_priorities.FiveLevelNaturalNT,
    natural_priorities.FiveLevelNaturalMajor,
])

natural_suited_part_scores = set([
    natural_priorities.TwoLevelNaturalMinor,
    natural_priorities.TwoLevelNaturalMajor,
    natural_priorities.ThreeLevelNaturalMinor,
    natural_priorities.ThreeLevelNaturalMajor,
    natural_priorities.FourLevelNaturalMinor,
])

natural_nt_part_scores = set([
    natural_priorities.OneLevelNaturalNT,
    natural_priorities.TwoLevelNaturalNT,
])

class Natural(Rule):
    # FIXME: This should have a SomeoneOpened() precondition.
    category = categories.Natural


class SuitedToPlay(Natural):
    preconditions = [
        MinimumCombinedPointsPrecondition(12),
        PartnerHasAtLeastLengthInSuit(1)
    ]
    constraints = {
        ('2C', '2D'): (MinimumCombinedPoints(19), natural_priorities.TwoLevelNaturalMinor),
        ('2H', '2S'): (MinimumCombinedPoints(19), natural_priorities.TwoLevelNaturalMajor),

        ('3C', '3D'): (MinimumCombinedPoints(22), natural_priorities.ThreeLevelNaturalMinor),
        ('3H', '3S'): (MinimumCombinedPoints(22), natural_priorities.ThreeLevelNaturalMajor),

        ('4C', '4D'): (MinimumCombinedPoints(25), natural_priorities.FourLevelNaturalMinor),
        ('4H', '4S'): (MinimumCombinedPoints(25), natural_priorities.FourLevelNaturalMajor),

        ('5C', '5D'): (MinimumCombinedPoints(28), natural_priorities.FiveLevelNaturalMinor),
        ('5H', '5S'): (MinimumCombinedPoints(28), natural_priorities.FiveLevelNaturalMajor),

        ('6C', '6D'): (MinimumCombinedPoints(33), natural_priorities.SixLevelNaturalMinor),
        ('6H', '6S'): (MinimumCombinedPoints(33), natural_priorities.SixLevelNaturalMajor),

        ('7C', '7D'): (MinimumCombinedPoints(37), natural_priorities.SevenLevelNaturalMinor),
        ('7H', '7S'): (MinimumCombinedPoints(37), natural_priorities.SevenLevelNaturalMajor),
    }
    shared_constraints = [MinimumCombinedLength(8)]


class NotrumpToPlay(Natural):
    constraints = {
        '1N': [MinimumCombinedPoints(19), natural_priorities.OneLevelNaturalNT],
        '2N': [MinimumCombinedPoints(22), natural_priorities.TwoLevelNaturalNT],
        '3N': [MinimumCombinedPoints(25), natural_priorities.ThreeLevelNaturalNT],
        # FIXME: 4N should really be 25, but in order to make that work we need SlamIsRemotePass.
        '4N': [MinimumCombinedPoints(28), natural_priorities.FourLevelNaturalNT],
        '5N': [MinimumCombinedPoints(30), natural_priorities.FiveLevelNaturalNT],
        '6N': [MinimumCombinedPoints(33), natural_priorities.SixLevelNaturalNT],
        '7N': [MinimumCombinedPoints(37), natural_priorities.SevenLevelNaturalNT],
    }


opening_priorities = enum.Enum(
    "StrongTwoClubs",
    "NoTrumpOpening",
    "LongestMajor",
    "HigherMajor",
    "LowerMajor",
    "LongestMinor",
    "HigherMinor",
    "LowerMinor",
)
rule_order.order(*reversed(opening_priorities))


class Opening(Rule):
    annotations = annotations.Opening
    preconditions = NoOpening()


class OneLevelSuitOpening(Opening):
    shared_constraints = OpeningRuleConstraint()
    annotations_per_call = {
        '1C': annotations.BidClubs,
        '1D': annotations.BidDiamonds,
        '1H': annotations.BidHearts,
        '1S': annotations.BidSpades,
    }
    # FIXME: This shadows the "annotations" module for the rest of this class scope!
    annotations = annotations.OneLevelSuitOpening
    constraints = {
        '1C': (clubs >= 3, opening_priorities.LowerMinor),
        '1D': (diamonds >= 3, opening_priorities.HigherMinor),
        '1H': (hearts >= 5, opening_priorities.LowerMajor),
        '1S': (spades >= 5, opening_priorities.HigherMajor),
    }
    conditional_priorities_per_call = {
        '1C': [
            (clubs > diamonds, opening_priorities.LongestMinor),
            (z3.And(clubs == 3, diamonds == 3), opening_priorities.LongestMinor),
        ],
        '1D': [(diamonds > clubs, opening_priorities.LongestMinor)],
        '1H': [(hearts > spades, opening_priorities.LongestMajor)],
        '1S': [(spades > hearts, opening_priorities.LongestMajor)],
    }


class NoTrumpOpening(Opening):
    annotations = annotations.NoTrumpSystemsOn
    constraints = {
        '1N': z3.And(points >= 15, points <= 17, balanced),
        '2N': z3.And(points >= 20, points <= 21, balanced)
    }
    priority = opening_priorities.NoTrumpOpening


class StrongTwoClubs(Opening):
    annotations = annotations.StrongTwoClubOpening
    call_names = '2C'
    shared_constraints = points >= 22  # FIXME: Should support "or 9+ winners"
    priority = opening_priorities.StrongTwoClubs


response_priorities = enum.Enum(
    "NegativeDouble",
    "Jacoby2N",
    "JumpShiftResponseToOpen",

    "MajorJumpToGame",
    "MajorLimitRaise",
    "MajorMinimumRaise",

    "LongestNewMajor",
    "OneSpadeWithFiveResponse",
    "OneHeartWithFiveResponse",
    "OneDiamondResponse",
    "OneHeartWithFourResponse",
    "OneSpadeWithFourResponse",

    "TwoHeartNewSuitResponse",
    "TwoSpadeNewSuitResponse",
    "TwoClubNewSuitResponse",
    "TwoDiamondNewSuitResponse",

    "MinorLimitRaise",
    "TwoNotrumpLimitResponse",
    "MinorMinimumRaise",
    "OneNotrumpResponse",
)
rule_order.order(*reversed(response_priorities))


class Response(Rule):
    preconditions = [LastBidHasAnnotation(positions.Partner, annotations.Opening)]


class ResponseToOneLevelSuitedOpen(Response):
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.OneLevelSuitOpening),
    ]


class OneLevelNewSuitResponse(ResponseToOneLevelSuitedOpen):
    shared_constraints = points >= 6
    constraints = {
        '1D': (diamonds >= 4, response_priorities.OneDiamondResponse),
        '1H': (hearts >= 4, response_priorities.OneHeartWithFourResponse),
        '1S': (spades >= 4, response_priorities.OneSpadeWithFourResponse),
    }
    # FIXME: 4 should probably be the special case and 5+ be the default priority.
    conditional_priorities_per_call = {
        '1H': [
            (z3.And(hearts >= 5, hearts > spades), response_priorities.LongestNewMajor),
            (hearts >= 5, response_priorities.OneHeartWithFiveResponse),
        ],
        '1S': [(spades >= 5, response_priorities.OneSpadeWithFiveResponse)]
    }


class OneNotrumpResponse(ResponseToOneLevelSuitedOpen):
    call_names = '1N'
    shared_constraints = points >= 6
    priority = response_priorities.OneNotrumpResponse


class RaiseResponse(ResponseToOneLevelSuitedOpen):
    preconditions = [
        RaiseOfPartnersLastSuit(),
        LastBidHasAnnotation(positions.Partner, annotations.Opening)
    ]


class MajorMinimumRaise(RaiseResponse):
    call_names = ['2H', '2S']
    shared_constraints = [MinimumCombinedLength(8), MinimumCombinedPoints(18)]
    priority = response_priorities.MajorMinimumRaise


class MajorLimitRaise(RaiseResponse):
    call_names = ['3H', '3S']
    shared_constraints = [MinimumCombinedLength(8), MinimumCombinedPoints(22)]
    priority = response_priorities.MajorLimitRaise


class MajorJumpToGame(RaiseResponse):
    call_names = ['4H', '4S']
    shared_constraints = [MinimumCombinedLength(10), points < 10]
    priority = response_priorities.MajorJumpToGame


class MinorMinimumRaise(RaiseResponse):
    call_names = ['2C', '2D']
    shared_constraints = [MinimumCombinedLength(8), MinimumCombinedPoints(18)]
    priority = response_priorities.MinorMinimumRaise


class MinorLimitRaise(RaiseResponse):
    call_names = ['3C', '3D']
    shared_constraints = [MinimumCombinedLength(8), MinimumCombinedPoints(22)]
    priority = response_priorities.MinorLimitRaise


class TwoNotrumpLimitResponse(ResponseToOneLevelSuitedOpen):
    preconditions = LastBidHasStrain(positions.Partner, [suit.CLUBS, suit.DIAMONDS])
    call_names = '2N'
    shared_constraints = [balanced, MinimumCombinedPoints(22)]
    priority = response_priorities.TwoNotrumpLimitResponse

# We should bid longer suits when possible, up the line for 4 cards.
# we don't currently bid 2D over 2C when we have longer diamonds.

class NewSuitAtTheTwoLevel(ResponseToOneLevelSuitedOpen):
    preconditions = [UnbidSuit(), NotJumpFromLastContract()]
    constraints = {
        '2C' : (clubs >= 4, response_priorities.TwoClubNewSuitResponse),
        '2D' : (diamonds >= 4, response_priorities.TwoDiamondNewSuitResponse),
        '2H' : (hearts >= 5, response_priorities.TwoHeartNewSuitResponse),
        '2S' : (spades >= 5, response_priorities.TwoSpadeNewSuitResponse),
    }
    shared_constraints = MinimumCombinedPoints(22)


class ResponseToMajorOpen(ResponseToOneLevelSuitedOpen):
    preconditions = [
        LastBidHasStrain(positions.Partner, suit.MAJORS),
        InvertedPrecondition(LastBidHasAnnotation(positions.Partner, annotations.Artificial))
    ]


class Jacoby2N(ResponseToMajorOpen):
    preconditions = LastBidWas(positions.RHO, 'P')
    call_names = '2N'
    shared_constraints = [points >= 14, SupportForPartnerLastBid(4)]
    priority = response_priorities.Jacoby2N
    annotations = annotations.Jacoby2N


jacoby_2n_response_priorities = enum.Enum(
    # Currently favoring features over slam interest.  Unclear if that's correct?
    "SolidSuit",
    "Singleton",
    "Slam",
    "Notrump",
    "MinimumGame",
)
rule_order.order(*reversed(jacoby_2n_response_priorities))


class ResponseToJacoby2N(Rule):
    # Bids above 4NT are either natural or covered by other conventions.
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Jacoby2N)
    category = categories.Gadget


class SingletonResponseToJacoby2N(ResponseToJacoby2N):
    preconditions = InvertedPrecondition(RebidSameSuit())
    call_names = ['3C', '3D', '3H', '3S']
    shared_constraints = MaxLength(1)
    annotations = annotations.Artificial
    priority = jacoby_2n_response_priorities.Singleton


class SolidSuitResponseToJacoby2N(ResponseToJacoby2N):
    preconditions = InvertedPrecondition(RebidSameSuit())
    call_names = ['4C', '4D', '4H', '4S']
    shared_constraints = [MinLength(5), ThreeOfTheTopFiveOrBetter()]
    priority = jacoby_2n_response_priorities.SolidSuit


class SlamResponseToJacoby2N(ResponseToJacoby2N):
    preconditions = RebidSameSuit()
    call_names = ['3C', '3D', '3H', '3S']
    shared_constraints = points >= 18
    priority = jacoby_2n_response_priorities.Slam


class MinimumResponseToJacoby2N(ResponseToJacoby2N):
    preconditions = RebidSameSuit()
    call_names = ['4C', '4D', '4H', '4S']
    shared_constraints = NO_CONSTRAINTS
    priority = jacoby_2n_response_priorities.MinimumGame


class NotrumpResponseToJacoby2N(ResponseToJacoby2N):
    call_names = ['3N']
    shared_constraints = points > 15 # It's really 15-17
    priority = jacoby_2n_response_priorities.Notrump


class JumpShift(object):
    preconditions = [UnbidSuit(), JumpFromLastContract(exact_size=1)]


class JumpShiftResponseToOpen(ResponseToOneLevelSuitedOpen):
    preconditions = JumpShift.preconditions
    # Jumpshifts must be below game and are off in competition so
    # 1S P 3H is the highest available response jumpshift.
    call_names = ['2D', '2H', '2S', '3C', '3D', '3H']
    # FIXME: Shouldn't this be MinHighCardPoints?
    shared_constraints = [points >= 19, MinLength(5)]
    priority = response_priorities.JumpShiftResponseToOpen


class ShapeForNegativeDouble(Constraint):
    def expr(self, history, call):
        call_string = '%s %s' % (history.partner.last_call.name, history.rho.last_call.name)
        return {
            '1C 1D': z3.And(hearts >= 4, spades >= 4),
            '1C 1H': spades == 4,
            '1C 1S': z3.And(diamonds >= 3, hearts >= 4),
            '1C 2D': z3.And(hearts >= 4, spades >= 4),
            '1C 2H': z3.And(diamonds >= 3, spades >= 4),
            '1C 2S': z3.And(diamonds >= 3, hearts >= 4),
            '1D 1H': spades == 4,
            '1D 1S': z3.And(clubs >= 3, hearts >= 4),
            '1D 2C': z3.And(hearts >= 4, spades >= 4),
            '1D 2H': z3.And(clubs >= 3, spades >= 4),
            '1D 2S': z3.And(clubs >= 3, hearts >= 4),
            '1H 1S': z3.And(clubs >= 3, diamonds >= 3), # Probably promises 4+ in both minors?
            '1H 2C': z3.And(diamonds >= 3, spades >= 4),
            '1H 2D': z3.And(clubs >= 3, spades >= 4),
            '1H 2S': z3.And(clubs >= 3, diamonds >= 3),
            '1S 2C': z3.And(diamonds >= 3, hearts >= 4),
            '1S 2D': z3.And(clubs >= 3, hearts >= 4),
            '1S 2H': z3.And(clubs >= 3, diamonds >= 3),
        }[call_string]


class NegativeDouble(ResponseToOneLevelSuitedOpen):
    call_names = 'X'
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.OneLevelSuitOpening),
        LastBidHasSuit(positions.Partner),
        LastBidHasSuit(positions.RHO),
        # A hackish way to make sure Partner and RHO did not bid the same suit.
        InvertedPrecondition(LastBidHasAnnotation(positions.RHO, annotations.Artificial)),
    ]
    shared_constraints = ShapeForNegativeDouble()
    priority = response_priorities.NegativeDouble
    annotations = annotations.NegativeDouble


class OneLevelNegativeDouble(NegativeDouble):
    preconditions = LastBidHasLevel(positions.RHO, 1)
    shared_constraints = points >= 6


class TwoLevelNegativeDouble(NegativeDouble):
    preconditions = LastBidHasLevel(positions.RHO, 2)
    shared_constraints = points >= 8


two_clubs_response_priorities = enum.Enum(
    "SuitResponse",
    "NoBiddableSuit",
    "WaitingResponse",
)
rule_order.order(*reversed(two_clubs_response_priorities))


class ResponseToStrongTwoClubs(Response):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.StrongTwoClubOpening)


class WaitingResponseToStrongTwoClubs(ResponseToStrongTwoClubs):
    call_names = '2D'
    shared_constraints = NO_CONSTRAINTS
    annotations = annotations.Artificial
    priority = two_clubs_response_priorities.WaitingResponse


class SuitResponseToStrongTwoClubs(ResponseToStrongTwoClubs):
    call_names = ['2H', '2S', '3C', '3D']
    shared_constraints = [MinLength(5), TwoOfTheTopThree(), points >= 8]
    # FIXME: These should have ordered conditional priorites, no?
    priority = two_clubs_response_priorities.SuitResponse


class NotrumpResponseToStrongTwoClubs(ResponseToStrongTwoClubs):
    call_names = '2N'
    shared_constraints = points >= 8
    priority = two_clubs_response_priorities.NoBiddableSuit


opener_rebid_priorities = enum.Enum(
    "SupportMajorMax",
    "SupportMajorLimit",
    "SupportMajorMin",

    "TwoNoTrumpOpenerRebid",
    "JumpShiftByOpener",
    "HelpSuitGameTry",

    # FIXME: 1S P 2D looks like this will will prefer 3C over 2S!
    "NewSuitClubs",
    "NewSuitDiamonds",
    "NewSuitHearts",
    "NewSuitSpades",

    "ReverseDiamonds",
    "ReverseHearts",
    "ReverseSpades",

    "GameForcingUnsupportedRebidByOpener",
    "InvitationalUnsupportedRebidByOpener",
    "UnforcedRebidOriginalSuit",
    "RebidOneNotrump",
    "ForcedRebidOriginalSuit",
)
rule_order.order(*reversed(opener_rebid_priorities))


class OpenerRebid(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Opening)


class RebidAfterOneLevelOpen(OpenerRebid):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.OneLevelSuitOpening),


class TwoNoTrumpOpenerRebid(RebidAfterOneLevelOpen):
    annotations = annotations.NoTrumpSystemsOn
    constraints = {
        '2N': z3.And(points >= 18, points <= 19, balanced)
    }
    priority = opener_rebid_priorities.TwoNoTrumpOpenerRebid


class RebidOneNotrumpByOpener(RebidAfterOneLevelOpen):
    preconditions = InvertedPrecondition(LastBidWas(positions.Partner, 'P'))
    call_names = '1N'
    priority = opener_rebid_priorities.RebidOneNotrump
    shared_constraints = NO_CONSTRAINTS


class NewOneLevelMajorByOpener(RebidAfterOneLevelOpen):
    preconditions = UnbidSuit()
    constraints = {
        '1H': (NO_CONSTRAINTS, opener_rebid_priorities.NewSuitHearts),
        '1S': (NO_CONSTRAINTS, opener_rebid_priorities.NewSuitSpades),
    }
    shared_constraints = MinLength(4)


class SecondSuitFromOpener(RebidAfterOneLevelOpen):
    preconditions = [
        NotJumpFromLastContract(),
        UnbidSuit(),
        InvertedPrecondition(HaveFit()),
    ]

class NewSuitByOpener(SecondSuitFromOpener):
    preconditions = SuitLowerThanMyLastSuit()
    constraints = {
        '2C': (NO_CONSTRAINTS, opener_rebid_priorities.NewSuitClubs),
        '2D': (NO_CONSTRAINTS, opener_rebid_priorities.NewSuitDiamonds),
        '2H': (NO_CONSTRAINTS, opener_rebid_priorities.NewSuitHearts),
        # 2S would necessarily be a reverse, or a jump shift, and is not covered by this rule.

        '3C': (MinimumCombinedPoints(25), opener_rebid_priorities.NewSuitClubs),
        '3D': (MinimumCombinedPoints(25), opener_rebid_priorities.NewSuitDiamonds),
        '3H': (MinimumCombinedPoints(25), opener_rebid_priorities.NewSuitHearts),
        # 3S would necessarily be a reverse, or a jump shift, and is not covered by this rule.
    }
    shared_constraints = MinLength(4)


reverse_preconditions = [
    InvertedPrecondition(SuitLowerThanMyLastSuit()),
    LastBidHasSuit(positions.Me),
    UnbidSuit(),
    NotJumpFromLastContract(),
]


class ReverseByOpener(SecondSuitFromOpener):
    preconditions = reverse_preconditions
    constraints = {
        # 2C is never a reverse
        '2D': (MinimumCombinedPoints(22), opener_rebid_priorities.ReverseDiamonds),
        '2H': (MinimumCombinedPoints(22), opener_rebid_priorities.ReverseHearts),
        '2S': (MinimumCombinedPoints(22), opener_rebid_priorities.ReverseSpades),

        # 3C is also never a reverse
        '3D': (MinimumCombinedPoints(25), opener_rebid_priorities.ReverseDiamonds),
        '3H': (MinimumCombinedPoints(25), opener_rebid_priorities.ReverseHearts),
        '3S': (MinimumCombinedPoints(25), opener_rebid_priorities.ReverseSpades),
    }
    shared_constraints = MinLength(4)


class SupportPartnerSuit(RebidAfterOneLevelOpen):
    preconditions = [
        InvertedPrecondition(RebidSameSuit()),
        RaiseOfPartnersLastSuit(),
    ]


class SupportPartnerMajorSuit(SupportPartnerSuit):
    constraints = {
        ('2H', '2S'): (NO_CONSTRAINTS, opener_rebid_priorities.SupportMajorMin),
        ('3H', '3S'): (MinimumCombinedPoints(22), opener_rebid_priorities.SupportMajorLimit),
        ('4H', '4S'): (MinimumCombinedPoints(25), opener_rebid_priorities.SupportMajorMax),
    }
    shared_constraints = MinimumCombinedLength(8)


class RebidOriginalSuitByOpener(RebidAfterOneLevelOpen):
    preconditions = [
        LastBidHasLevel(positions.Me, 1),
        RebidSameSuit(),
    ]


class MinimumRebidOriginalSuitByOpener(RebidOriginalSuitByOpener):
    preconditions = NotJumpFromLastContract()


class UnforcedRebidOriginalSuitByOpener(MinimumRebidOriginalSuitByOpener):
    preconditions = InvertedPrecondition(ForcedToBid())
    call_names = ['2C', '2D', '2H', '2S']
    shared_constraints = MinLength(6)
    priority = opener_rebid_priorities.UnforcedRebidOriginalSuit


class ForcedRebidOriginalSuitByOpener(MinimumRebidOriginalSuitByOpener):
    preconditions = ForcedToBid()
    call_names = ['2C', '2D', '2H', '2S']
    conditional_priorities = [
        (MinLength(6), opener_rebid_priorities.UnforcedRebidOriginalSuit),
    ]
    shared_constraints = MinLength(5)


class UnsupportedRebid(RebidOriginalSuitByOpener):
    preconditions = MaxShownLength(positions.Partner, 0)


class InvitationalUnsupportedRebidByOpener(UnsupportedRebid):
    preconditions = JumpFromLastContract()
    call_names = ['3C', '3D', '3H', '3S']
    shared_constraints = MinLength(6), points >= 16
    priority = opener_rebid_priorities.InvitationalUnsupportedRebidByOpener


class GameForcingUnsupportedRebidByOpener(UnsupportedRebid):
    preconditions = JumpFromLastContract()
    call_names = ['4C', '4D', '4H', '4S']
    shared_constraints = MinLength(6), points >= 19
    priority = opener_rebid_priorities.GameForcingUnsupportedRebidByOpener


class HelpSuitGameTry(RebidAfterOneLevelOpen):
    preconditions = [
        NotJumpFromLastContract(),
        HaveFit(),
        UnbidSuit(),
    ]
    # Minimum: 1C,2C,2D, Max: 1C,3C,3S
    call_names = [
              '2D', '2H', '2S',
        '3C', '3D', '3H', '3S'
    ]
    # Descriptive not placement bid hence points instead of MinimumCombinedPoints.
    shared_constraints = [MinLength(4), Stopper(), points >= 16]
    priority = opener_rebid_priorities.HelpSuitGameTry


class JumpShiftByOpener(RebidAfterOneLevelOpen):
    preconditions = JumpShift.preconditions
    # The lowest possible jumpshift is 1C P 1D P 2H.
    # The highest possible jumpshift is 1S P 2H P 4D
    call_names = [
                    '2H', '2S',
        '3C', '3D', '3H', '3S',
        '4C', '4D'
    ]
    # FIXME: The book mentions that opener jumpshifts don't always promise 4, especially for 1C P MAJOR P 3D
    shared_constraints = (points >= 19, MinLength(4))
    priority = opener_rebid_priorities.JumpShiftByOpener


two_clubs_opener_rebid_priorities = enum.Enum(
    "ThreeLevelNTRebid",
    "SuitedJumpRebid", # This isn't actually comparible with 3N.

    "SuitedRebid", # I think you'd rather bid 2S when available, instead of 2N, right?
    "TwoLevelNTRebid",
)
rule_order.order(*reversed(two_clubs_opener_rebid_priorities))


class OpenerRebidAfterStrongTwoClubs(OpenerRebid):
    preconditions = LastBidWas(positions.Me, '2C')
    # This could also alternatively use annotations.StrongTwoClubOpening


class NotrumpRebidOverTwoClubs(OpenerRebidAfterStrongTwoClubs):
    annotations = annotations.NoTrumpSystemsOn
    # These bids are only systematic after a 2D response from partner.
    preconditions = LastBidWas(positions.Partner, '2D')
    constraints = {
        '2N': [points >= 22, two_clubs_opener_rebid_priorities.TwoLevelNTRebid],
        '3N': [points >= 25, two_clubs_opener_rebid_priorities.ThreeLevelNTRebid], # Should this cap at 27?
    }
    shared_constraints = balanced


class OpenerSuitedRebidAfterStrongTwoClubs(OpenerRebidAfterStrongTwoClubs):
    preconditions = [UnbidSuit(), NotJumpFromLastContract()]
    # This maxes out at 4C -> 2C P 3D P 4C
    # If the opponents are competing we're just gonna double them anyway.
    call_names = [
                '2H', '2S',
    '3C', '3D', '3H', '3S',
    '4C']
    # FIXME: This should either have NoMajorFit(), or have priorities separated
    # so that we prefer to support our partner's major before bidding our own new minor.
    shared_constraints = MinLength(5)
    priority = two_clubs_opener_rebid_priorities.SuitedRebid


class OpenerSuitedJumpRebidAfterStrongTwoClubs(OpenerRebidAfterStrongTwoClubs):
    preconditions = [UnbidSuit(), JumpFromLastContract(exact_size=1)]
    # This maxes out at 4C -> 2C P 3D P 5C, but I'm not sure we need to cover that case?
    # If we have self-supporting suit why jump all the way to 5C?  Why not Blackwood in preparation for slam?
    call_names = ['3H', '3S', '4C', '4D', '4H', '4S', '5C']
    shared_constraints = [MinLength(7), TwoOfTheTopThree()]
    priority = two_clubs_opener_rebid_priorities.SuitedJumpRebid


responder_rebid_priorities = enum.Enum(
    "JumpShiftResponderRebid",
    "ResponderReverse",
    "ThreeLevelSuitRebidByResponder",
    "RebidResponderSuitByResponder",
)
rule_order.order(*reversed(responder_rebid_priorities))


sign_off_priorities = enum.Enum(
    "ResponderSignoffInMinorGame",
    "ResponderSignoffInPartnersSuit",
)
rule_order.order(*reversed(sign_off_priorities))


class ResponderRebid(Rule):
    preconditions = [
        Opened(positions.Partner),
        HasBid(positions.Me),
    ]


class OneLevelOpeningResponderRebid(ResponderRebid):
    preconditions = OneLevelSuitedOpeningBook()


class ResponderSuitRebid(OneLevelOpeningResponderRebid):
    preconditions = RebidSameSuit()


class RebidResponderSuitByResponder(ResponderSuitRebid):
    preconditions = InvertedPrecondition(RaiseOfPartnersLastSuit())
    call_names = ['2D', '2H', '2S']
    shared_constraints = [MinLength(6), points >= 6]
    priority = responder_rebid_priorities.RebidResponderSuitByResponder


class ThreeLevelSuitRebidByResponder(ResponderSuitRebid):
    preconditions = [
        InvertedPrecondition(RaiseOfPartnersLastSuit()),
        MaxShownLength(positions.Partner, 0),
        MaxShownLength(positions.Me, 5)
    ]
    call_names = ['3C', '3D', '3H', '3S']
    shared_constraints = [MinLength(6), MinimumCombinedPoints(22)]
    priority = responder_rebid_priorities.ThreeLevelSuitRebidByResponder


class ResponderSignoffInPartnersSuit(OneLevelOpeningResponderRebid):
    preconditions = [
        InvertedPrecondition(RaiseOfPartnersLastSuit()),
        PartnerHasAtLeastLengthInSuit(3)
    ]
    call_names = ['2C', '2D', '2H', '2S']
    shared_constraints = MinimumCombinedLength(7)
    priority = sign_off_priorities.ResponderSignoffInPartnersSuit


# class ResponderSignoffInMinorGame(ResponderRebid):
#     preconditions = [
#         PartnerHasAtLeastLengthInSuit(3),
#         InvertedPrecondition(RebidSameSuit())
#     ]
#     constraints = {
#         '5C': MinimumCombinedPoints(25),
#         '5D': MinimumCombinedPoints(25),
#     }
#     shared_constraints = [MinimumCombinedLength(8), NoMajorFit()]
#     priority = sign_off_priorities.ResponderSignoffInMinorGame


class ResponderReverse(OneLevelOpeningResponderRebid):
    preconditions = reverse_preconditions
    # Min: 1C,1D,2C,2H, Max: 1S,2D,2S,3H
    call_names = [
                  '2H','2S',
        '3C','3D','3H',
    ]
    shared_constraints = [MinLength(4), points >= 12]
    priority = responder_rebid_priorities.ResponderReverse


class JumpShiftResponderRebid(OneLevelOpeningResponderRebid):
    preconditions = JumpShift.preconditions
    # Smallest: 1C,1D,1H,2S
    # Largest: 1S,2H,3C,4D (anything above 4D is game)
    call_names = [
                          '2S',
        '3C', '3D', '3H', '3S',
        '4C', '4D'
    ]
    shared_constraints = [MinLength(4), points >= 14]
    priority = responder_rebid_priorities.JumpShiftResponderRebid


# FIXME: We should add an OpenerRebid of 3N over 2C P 2N P to show a minimum 22-24 HCP
# instead of jumping to 5N which just wastes bidding space.
# This is not covered in the book or the SAYC pdf.


class SecondNegative(ResponderRebid):
    # FIXME: This should not apply over 2N, but currently ForcedToBid thinks that all
    # bids of 17+ are forcing forever. :(
    preconditions = [
        StrongTwoClubOpeningBook(),
        LastBidWas(positions.Me, '2D'),
        ForcedToBid(),
    ]
    call_names = '3C'
    # Denies a fit, shows a max of 3 hcp
    shared_constraints = NO_CONSTRAINTS
    annotations = annotations.Artificial


nt_response_priorities = enum.Enum(
    "QuantitativeFourNotrumpJump",
    "LongMajorSlamInvitation",
    "MinorGameForceStayman",
    "FourFiveStayman",
    "JacobyTransferToLongerMajor",
    "JacobyTransferToSpadesWithGameForcingValues",
    "JacobyTransferToHeartsWithGameForcingValues",
    "JacobyTransferToHearts",
    "JacobyTransferToSpades",
    "Stayman",
    "NotrumpGameAccept",
    "NotrumpGameInvitation",
    "LongMinorGameInvitation",
    "TwoSpadesRelay",
    "GarbageStayman",
)
rule_order.order(*reversed(nt_response_priorities))


class NoTrumpResponse(Rule):
    category = categories.NoTrumpSystem
    preconditions = [
        # 1N overcalls have systems on too, partner does not have to have opened
        LastBidHasAnnotation(positions.Partner, annotations.NoTrumpSystemsOn),
    ]


class NotrumpGameInvitation(NoTrumpResponse):
    # This is an explicit descriptive rule, not a ToPlay rule.
    # ToPlay is 7-9, but 7 points isn't in game range.
    constraints = { '2N': points >= 8 }
    priority = nt_response_priorities.NotrumpGameInvitation


class NotrumpGameAccept(NoTrumpResponse):
    # This is an explicit descriptive rule, not a ToPlay rule.
    # ToPlay is 7-9, but 7 points isn't in game range.
    constraints = { '3N': points >= 10 }
    priority = nt_response_priorities.NotrumpGameAccept


two_club_stayman_constraint = ConstraintAnd(
    MinimumCombinedPoints(23),
    z3.Or(hearts >= 4, spades >= 4)
)


four_five_stayman_constraint = ConstraintAnd(
    MinimumCombinedPoints(23),
    z3.Or(
        z3.And(hearts == 4, spades == 5),
        z3.And(hearts == 5, spades == 4),
    ),
)

minor_game_force_stayman_constraints = z3.And(
    points >= 13,
    z3.Or(clubs >= 5, diamonds >= 5)
)

# 2C is a very special snowflake and can lead into many sequences, thus it gets its own class.
class TwoLevelStayman(NoTrumpResponse):
    annotations = annotations.Stayman
    call_names = '2C'

    shared_constraints = ConstraintOr(
        minor_game_force_stayman_constraints,
        two_club_stayman_constraint,
        # Garbage stayman is a trade-off.  The fewer points you have the less likely
        # your partner will make 1N.  2D with only 6 is better than 1N with only 18 points.
        z3.And(spades >= 3, hearts >= 3, 
            z3.Or(diamonds >= 5,
                z3.And(diamonds >= 4, points <= 3)
            ),
        ),
    )
    conditional_priorities = [
        (minor_game_force_stayman_constraints, nt_response_priorities.MinorGameForceStayman),
        (four_five_stayman_constraint, nt_response_priorities.FourFiveStayman),
        (two_club_stayman_constraint, nt_response_priorities.Stayman),
    ]
    priority = nt_response_priorities.GarbageStayman


class BasicStayman(NoTrumpResponse):
    annotations = annotations.Stayman
    priority = nt_response_priorities.Stayman
    shared_constraints = [z3.Or(hearts >= 4, spades >= 4)]


class ThreeLevelStayman(BasicStayman):
    preconditions = NotJumpFromPartnerLastBid()
    constraints = { '3C': MinimumCombinedPoints(25) }


class StolenTwoClubStayman(BasicStayman):
    preconditions = LastBidWas(positions.RHO, '2C')
    constraints = { 'X': MinimumCombinedPoints(23) }


class StolenThreeClubStayman(BasicStayman):
    preconditions = LastBidWas(positions.RHO, '3C')
    constraints = { 'X': MinimumCombinedPoints(25) }


class NoTrumpTransferResponse(NoTrumpResponse):
    annotations = annotations.Transfer


class JacobyTransferToHearts(NoTrumpTransferResponse):
    call_names = '2D'
    shared_constraints = hearts >= 5
    conditional_priorities = [
        (hearts > spades, nt_response_priorities.JacobyTransferToLongerMajor),
        (z3.And(hearts == spades, points >= 10), nt_response_priorities.JacobyTransferToHeartsWithGameForcingValues),
    ]
    priority = nt_response_priorities.JacobyTransferToHearts


class JacobyTransferToSpades(NoTrumpTransferResponse):
    call_names = '2H'
    shared_constraints = spades >= 5
    conditional_priorities = [
        (spades > hearts, nt_response_priorities.JacobyTransferToLongerMajor),
        (z3.And(hearts == spades, points >= 10), nt_response_priorities.JacobyTransferToSpadesWithGameForcingValues),
    ]
    priority = nt_response_priorities.JacobyTransferToSpades


class TwoSpadesRelay(NoTrumpTransferResponse):
    constraints = {
        '2S': z3.Or(diamonds >= 6, clubs >= 6),
    }
    priority = nt_response_priorities.TwoSpadesRelay


class QuantitativeFourNotrumpJumpConstraint(Constraint):
    def expr(self, history, call):
        # Invites opener to bid 6N if at a maxium, otherwise pass.
        return points + history.partner.max_points >= 33


class QuantitativeFourNotrumpJump(NoTrumpResponse):
    call_names = '4N'
    preconditions = JumpFromLastContract()
    shared_constraints = QuantitativeFourNotrumpJumpConstraint()
    priority = nt_response_priorities.QuantitativeFourNotrumpJump


class AcceptTransfer(Rule):
    category = categories.Relay
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.Transfer),
        NotJumpFromPartnerLastBid(),
    ]
    shared_constraints = NO_CONSTRAINTS
    annotations = annotations.Artificial
    priority = relay_priorities.Accept


class AcceptTransferToHearts(AcceptTransfer):
    preconditions = LastBidHasStrain(positions.Partner, suit.DIAMONDS)
    call_names = ['2H', '3H']


class AcceptTransferToSpades(AcceptTransfer):
    preconditions = LastBidHasStrain(positions.Partner, suit.HEARTS)
    call_names = ['2S', '3S']


class AcceptTransferToClubs(AcceptTransfer):
    preconditions = LastBidHasStrain(positions.Partner, suit.SPADES)
    call_names = '3C'


class SuperAcceptTransfer(Rule):
    category = categories.Relay
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.Transfer),
        JumpFromPartnerLastBid(exact_size=1),
    ]
    shared_constraints = points >= 17
    annotations = annotations.Artificial
    priority = relay_priorities.SuperAccept


class SuperAcceptTransferToHearts(SuperAcceptTransfer):
    preconditions = LastBidHasStrain(positions.Partner, suit.DIAMONDS)
    call_names = '3H'
    shared_constraints = hearts >=4


class SuperAcceptTransferToSpades(SuperAcceptTransfer):
    preconditions = LastBidHasStrain(positions.Partner, suit.HEARTS)
    call_names = '3S'
    shared_constraints = spades >=4


class ResponseAfterTransferToClubs(Rule):
    category = categories.Relay # Is this right?
    preconditions = [
        LastBidWas(positions.Partner, '3C'),
        LastBidHasAnnotation(positions.Me, annotations.Transfer),
    ]
    constraints = {
        'P': clubs >= 6,
        '3D': diamonds >= 6,
    }
    priority = relay_priorities.Accept # This priority is bogus.


stayman_response_priorities = enum.Enum(
    "HeartStaymanResponse",
    "SpadeStaymanResponse",
    "DiamondStaymanResponse",
    "PassStaymanResponse",
)
rule_order.order(*reversed(stayman_response_priorities))


class StaymanResponse(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Stayman)
    category = categories.NoTrumpSystem


class NaturalStaymanResponse(StaymanResponse):
    preconditions = NotJumpFromPartnerLastBid()
    constraints = {
        ('2H', '3H'): (hearts >= 4, stayman_response_priorities.HeartStaymanResponse),
        ('2S', '3S'): (spades >= 4, stayman_response_priorities.SpadeStaymanResponse),
    }


class PassStaymanResponse(StaymanResponse):
    call_names = 'P'
    shared_constraints = NO_CONSTRAINTS
    priority = stayman_response_priorities.PassStaymanResponse


class DiamondStaymanResponse(StaymanResponse):
    preconditions = NotJumpFromPartnerLastBid()
    call_names = ['2D', '3D']
    shared_constraints = NO_CONSTRAINTS
    priority = stayman_response_priorities.DiamondStaymanResponse
    annotations = annotations.Artificial


# FIXME: Need "Stolen" variants for 3-level.
class StolenHeartStaymanResponse(StaymanResponse):
    constraints = { 'X': hearts >= 4 }
    preconditions = LastBidWas(positions.RHO, '2H')
    priority = stayman_response_priorities.HeartStaymanResponse


class StolenSpadeStaymanResponse(StaymanResponse):
    constraints = { 'X': spades >= 4 }
    preconditions = LastBidWas(positions.RHO, '2S')
    priority = stayman_response_priorities.SpadeStaymanResponse


class OneNoTrumpResponse(NoTrumpResponse):
    preconditions = LastBidWas(positions.Partner, '1N')


class LongMinorGameInvitation(OneNoTrumpResponse):
    call_names = ['3C', '3D']
    shared_constraints = [MinLength(6), TwoOfTheTopThree(), points >= 5]
    # FIXME: Should use the longer suit preference pattern.
    priority = nt_response_priorities.LongMinorGameInvitation


class LongMajorSlamInvitation(OneNoTrumpResponse):
    call_names = ['3H', '3S']
    shared_constraints = [MinLength(6), TwoOfTheTopThree(), points >= 14]
    # FIXME: Should use the longer suit preference pattern.
    priority = nt_response_priorities.LongMajorSlamInvitation


class StaymanRebid(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Stayman)
    category = categories.NoTrumpSystem


class GarbagePassStaymanRebid(StaymanRebid):
    # GarbageStayman only exists at the 2-level
    preconditions = LastBidWas(positions.Me, '2C')
    call_names = 'P'
    shared_constraints = points <= 7


stayman_rebid_priorities = enum.Enum(
    "MinorGameForceRebid",
    "GameForcingOtherMajor",
    "InvitationalOtherMajor",
)
rule_order.order(*reversed(stayman_rebid_priorities))


class MinorGameForceRebid(StaymanRebid):
    call_names = ['3C', '3D']
    shared_constraints = [MinLength(5), minor_game_force_stayman_constraints]
    priority = stayman_rebid_priorities.MinorGameForceRebid


class OtherMajorRebidAfterStayman(StaymanRebid):
    preconditions = [
        InvertedPrecondition(RaiseOfPartnersLastSuit()),
    ]
    # Rebidding the other major shows 5-4, with invitational or game-force values.
    constraints = {
        '2H': ([points >= 8, hearts == 5, spades == 4], stayman_rebid_priorities.InvitationalOtherMajor),
        '2S': ([points >= 8, spades == 5, hearts == 4], stayman_rebid_priorities.InvitationalOtherMajor),

        # # Use MinimumCombinedPoints instead of MinHighCardPoints as 3-level bids
        # # are game forcing over both 2C and 3C Stayman responses.
        '3H': ([MinimumCombinedPoints(25), hearts == 5, spades == 4], stayman_rebid_priorities.GameForcingOtherMajor),
        '3S': ([MinimumCombinedPoints(25), spades == 5, hearts == 4], stayman_rebid_priorities.GameForcingOtherMajor),
    }


overcall_priorities = enum.Enum(
    "MichaelsCuebid",
    "Unusual2N",
    "DirectOvercall1N",
    "DirectNotrumpDouble",
    "TakeoutDouble",

    "WeakFourLevelPremptive",
    "WeakThreeLevelPremptive",
    "WeakTwoLevelPremptive",

    "DirectOvercallLongestMajor",
    "DirectOvercallMajor",
    "DirectOvercallLongestMinor",
    "DirectOvercallMinor",

    "FourLevelPremptive",
    "ThreeLevelPremptive",
    "TwoLevelPremptive",
)
rule_order.order(*reversed(overcall_priorities))


class DirectOvercall(Rule):
    preconditions = EitherPrecondition(
            LastBidHasAnnotation(positions.RHO, annotations.Opening),
            AndPrecondition(
                LastBidHasAnnotation(positions.LHO, annotations.Opening),
                LastBidWas(positions.Partner, 'P'),
                InvertedPrecondition(LastBidWas(positions.RHO, 'P'))
            )
        )


class BalancingOvercall(Rule):
    preconditions = [
        LastBidHasAnnotation(positions.LHO, annotations.Opening),
        LastBidWas(positions.Partner, 'P'),
        LastBidWas(positions.RHO, 'P'),
    ]


class StandardDirectOvercall(DirectOvercall):
    preconditions = [
        LastBidHasSuit(positions.RHO),
        NotJumpFromLastContract(),
        UnbidSuit(),
        # FIXME: We should not bid if we have 4 cards in their suit.
    ]
    shared_constraints = [MinLength(5), ThreeOfTheTopFiveOrBetter()]
    annotations = annotations.StandardOvercall


class OneLevelStandardOvercall(StandardDirectOvercall):
    shared_constraints = points >= 8


class OneDiamondOvercall(OneLevelStandardOvercall):
    call_names = '1D'
    priority = overcall_priorities.DirectOvercallMinor


class OneHeartOvercall(OneLevelStandardOvercall):
    call_names = '1H'
    conditional_priorities = [
        (hearts > spades, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class OneSpadeOvercall(OneLevelStandardOvercall):
    call_names = '1S'
    conditional_priorities = [
        (spades >= hearts, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class DirectNotrumpDouble(DirectOvercall):
    preconditions = LastBidWas(positions.RHO, '1N')
    call_names = 'X'
    shared_constraints = z3.And(points >= 15, points <= 17, balanced)
    priority = overcall_priorities.DirectNotrumpDouble


class TwoLevelStandardOvercall(StandardDirectOvercall):
    shared_constraints = points >= 10


class TwoClubOvercall(TwoLevelStandardOvercall):
    call_names = '2C'
    conditional_priorities = [
        (clubs > diamonds, overcall_priorities.DirectOvercallLongestMinor),
    ]
    priority = overcall_priorities.DirectOvercallMinor


class TwoDiamondOvercall(TwoLevelStandardOvercall):
    call_names = '2D'
    conditional_priorities = [
        (diamonds >= clubs, overcall_priorities.DirectOvercallLongestMinor),
    ]
    priority = overcall_priorities.DirectOvercallMinor


class TwoHeartOvercall(TwoLevelStandardOvercall):
    call_names = '2H'
    conditional_priorities = [
        (hearts > spades, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class TwoSpadeOvercall(TwoLevelStandardOvercall):
    call_names = '2S'
    conditional_priorities = [
        (spades >= hearts, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class ResponseToStandardOvercall(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.StandardOvercall)


# This is nearly identical to TheLaw, it just notes that you have 6 points.
# All it does is cause one test to fail.  It may not be worth having.
class RaiseResponseToStandardOvercall(ResponseToStandardOvercall):
    preconditions = [RaiseOfPartnersLastSuit(), NotJumpFromLastContract()]
    call_names = [
              '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
    ]
    shared_constraints = [MinLength(3), points >= 6]


class CuebidResponseToStandardOvercall(ResponseToStandardOvercall):
    preconditions = [
        CueBid(positions.LHO),
        NotJumpFromLastContract()
    ]
    call_names = [
        '2C', '2D', '2H', '2S',
        '3C', '3D', '3H',
    ]
    shared_constraints = [SupportForPartnerLastBid(3), points >= 11]


class NewSuitResponseToStandardOvercall(ResponseToStandardOvercall):
    preconditions = [
        TheyOpened(),
        InvertedPrecondition(LastBidWas(positions.Partner, 'P')),
        NotJumpFromLastContract(),
        UnbidSuit()
    ]
    call_names = [
                    '1H', '1S',
        '2C', '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
    ]
    shared_constraints = [
        MinLength(5),
        TwoOfTheTopThree(),
        MinCombinedPointsForPartnerMinimumSuitedRebid(),
    ]


class DirectOvercall1N(DirectOvercall):
    call_names = '1N'
    shared_constraints = [points >= 15, points <= 17, balanced, StopperInRHOSuit()]
    priority = overcall_priorities.DirectOvercall1N
    annotations = annotations.NoTrumpSystemsOn


class MichaelsCuebid(object):
    preconditions = [
        NotJumpFromLastContract(),
        InvertedPrecondition(UnbidSuit()),
        # Michaels is only on if the opponents have only bid one suit.
        UnbidSuitCountRange(3, 3),
    ]
    constraints = {
        ('2C', '2D', '3C', '3D'): z3.And(hearts >= 5, spades >= 5),
        ('2H', '3H'): z3.And(spades >= 5, z3.Or(clubs >= 5, diamonds >= 5)),
        ('2S', '3S'): z3.And(hearts >= 5, z3.Or(clubs >= 5, diamonds >= 5)),
    }
    priority = overcall_priorities.MichaelsCuebid
    annotations = annotations.MichaelsCuebid
    # FIXME: Should the hole in this point range be generated by a higher priority bid?
    shared_constraints = z3.Or(6 <= points <= 12, 15 <= points)


class DirectMichaelsCuebid(MichaelsCuebid, DirectOvercall):
    pass


class BalancingMichaelsCuebid(MichaelsCuebid, BalancingOvercall):
    pass


class Unusual2N(Rule):
    preconditions = [
        # Unusual2N only exists immediately after RHO opens.
        LastBidHasAnnotation(positions.RHO, annotations.Opening),
        JumpFromLastContract(),
    ]
    call_names = '2N'
    # FIXME: We should consider doing mini-max unusual 2N now that we can!
    shared_constraints = [Unusual2NShape(), points >= 6]
    annotations = annotations.Unusual2N
    priority = overcall_priorities.Unusual2N


class TakeoutDouble(Rule):
    call_names = 'X'
    preconditions = [
        LastBidHasSuit(),
        InvertedPrecondition(HasBid(positions.Partner)),
        # LastBidWasNaturalSuit(),
        # LastBidWasBelowGame(),
        UnbidSuitCountRange(2, 3),
    ]
    annotations = annotations.TakeoutDouble
    shared_constraints = ConstraintOr(SupportForUnbidSuits(), points >= 17)
    priority = overcall_priorities.TakeoutDouble


class OneLevelTakeoutDouble(TakeoutDouble):
    preconditions = Level(1)
    # FIXME: Why isn't this 12?  SuitedToPlay can only respond to 12+ points currently.
    shared_constraints = points >= 11


class TwoLevelTakeoutDouble(TakeoutDouble):
    preconditions = Level(2)
    shared_constraints = points >= 15


takeout_double_responses = enum.Enum(
    "ThreeNotrump",
    "CuebidResponseToTakeoutDouble",

    "JumpSpadeResonseToTakeoutDouble",
    "JumpHeartResonseToTakeoutDouble",

    "TwoNotrumpJump",

    "JumpDiamondResonseToTakeoutDouble",
    "JumpClubResonseToTakeoutDouble",

    "ThreeCardJumpSpadeResonseToTakeoutDouble",
    "ThreeCardJumpHeartResonseToTakeoutDouble",
    "ThreeCardJumpDiamondResonseToTakeoutDouble",
    "ThreeCardJumpClubResonseToTakeoutDouble",

    "SpadeResonseToTakeoutDouble",
    "HeartResonseToTakeoutDouble",

    "TwoNotrump",
    "OneNotrump",

    "DiamondResonseToTakeoutDouble",
    "ClubResonseToTakeoutDouble",

    "ThreeCardSpadeResonseToTakeoutDouble",
    "ThreeCardHeartResonseToTakeoutDouble",
    "ThreeCardDiamondResonseToTakeoutDouble",
    "ThreeCardClubResonseToTakeoutDouble",
)
rule_order.order(*reversed(takeout_double_responses))


# Response indicates longest suit (excepting opponent's) with 3+ cards support.
# Cheapest level indicates < 10 points.
# NT indicates a stopper in opponent's suit.  1N: 6-10, 2N: 11-12, 3N: 13-16
# Jump bid indicates 10-12 points (normal invitational values)
# cue-bid in opponent's suit is a 13+ michaels-like bid.
class ResponseToTakeoutDouble(Rule):
    preconditions = [
        LastBidWas(positions.RHO, 'P'),
        LastBidHasAnnotation(positions.Partner, annotations.TakeoutDouble),
    ]


class NotrumpResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = [NotJumpFromLastContract()]
    constraints = {
        '1N': (points >= 6, takeout_double_responses.OneNotrump),
        '2N': (points >= 11, takeout_double_responses.TwoNotrump),
        '3N': (points >= 13, takeout_double_responses.ThreeNotrump),
    }
    shared_constraints = [balanced, StoppersInOpponentsSuits()]


# FIXME: This could probably be handled by suited to play if we could get the priorities right!
class JumpNotrumpResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = [JumpFromLastContract()]
    constraints = {
        '2N': (points >= 11, takeout_double_responses.TwoNotrumpJump),
        '3N': (points >= 13, takeout_double_responses.ThreeNotrump),
    }
    shared_constraints = [balanced, StoppersInOpponentsSuits()]


class SuitResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = [UnbidSuit(), NotJumpFromLastContract()]
    # FIXME: Why is the min-length constraint necessary?
    shared_constraints = [MinLength(3), LongestSuitExceptOpponentSuits()]
    # Need conditional priorities to disambiguate cases like being 1.4.4.4 with 0 points after 1C X P
    # Similarly after 1H X P, with 4 spades and 4 clubs, but with xxxx spades and AKQx clubs, do we bid clubs or spades?
    constraints = {
        (      '2C', '3C'): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardClubResonseToTakeoutDouble),
        ('1D', '2D', '3D'): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardDiamondResonseToTakeoutDouble),
        ('1H', '2H', '3H'): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardHeartResonseToTakeoutDouble),
        ('1S', '2S'      ): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardSpadeResonseToTakeoutDouble),
    }
    conditional_priorities_per_call = {
        (      '2C', '3C'): [(clubs >= 4, takeout_double_responses.ClubResonseToTakeoutDouble)],
        ('1D', '2D', '3D'): [(diamonds >= 4, takeout_double_responses.DiamondResonseToTakeoutDouble)],
        ('1H', '2H', '3H'): [(hearts >= 4, takeout_double_responses.HeartResonseToTakeoutDouble)],
        ('1S', '2S'      ): [(spades >= 4, takeout_double_responses.SpadeResonseToTakeoutDouble)],
    }


class JumpSuitResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = [UnbidSuit(), JumpFromLastContract(exact_size=1)]
    # You can have 10 points, but no stopper in opponents suit and only a 3 card suit to bid.
    # 1C X P, xxxx.Axx.Kxx.Kxx
    shared_constraints = [MinLength(3), LongestSuitExceptOpponentSuits(), points >= 10]
    constraints = {
        (      '3C', '4C'): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardJumpClubResonseToTakeoutDouble),
        ('2D', '3D', '4D'): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardJumpDiamondResonseToTakeoutDouble),
        ('2H', '3H', '4H'): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardJumpHeartResonseToTakeoutDouble),
        ('2S', '3S'      ): (NO_CONSTRAINTS, takeout_double_responses.ThreeCardJumpSpadeResonseToTakeoutDouble),
    }
    conditional_priorities_per_call = {
        (      '3C', '4C'): [(clubs >= 4, takeout_double_responses.JumpClubResonseToTakeoutDouble)],
        ('2D', '3D', '4D'): [(diamonds >= 4, takeout_double_responses.JumpDiamondResonseToTakeoutDouble)],
        ('2H', '3H', '4H'): [(hearts >= 4, takeout_double_responses.JumpHeartResonseToTakeoutDouble)],
        ('2S', '3S'      ): [(spades >= 4, takeout_double_responses.JumpSpadeResonseToTakeoutDouble)],
    }


class CuebidResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = [CueBid(positions.LHO), NotJumpFromLastContract()]
    priority = takeout_double_responses.CuebidResponseToTakeoutDouble
    call_names = (
        '2C', '2D', '2H', '2S',
        '3C', '3D', '3H', '3S'
    )
    # FIXME: 4+ in the available majors?
    shared_constraints = [points >= 13, SupportForUnbidSuits()]


# NOTE: I don't think we're going to end up needing most of these.
rebids_after_takeout_double = enum.Enum(
    "CueBidAfterTakeoutDouble",

    "JumpMajorRaise",
    "MajorRaise",

    "ThreeNotrumpAfterTakeoutDouble",

    "JumpSpadesSuit",
    "SpadesNewSuit",
    "JumpHeartsSuit",
    "HeartsNewSuit",

    "TwoNotrumpAfterTakeoutDouble",
    "OneNotrumpAfterTakeoutDouble",

    "JumpMinorRaise",
    "MinorRaise",

    "JumpDiamondsNewSuit",
    "DiamondsNewSuit",
    "JumpClubsNewSuit",
    "ClubsNewSuit",
)
rule_order.order(*reversed(rebids_after_takeout_double))


class RebidAfterTakeoutDouble(Rule):
    # FIXME: These only apply after a minimum (non-jump?) response from partner.
    preconditions = LastBidHasAnnotation(positions.Me, annotations.TakeoutDouble)
    shared_constraints = points >= 17


# class PassAfterTakeoutDouble(Rule):
#     preconditions = [
#         LastBidHasAnnotation(positions.Me, annotations.TakeoutDouble)
#         LastBidWas(positions.RHO, 'P')
#     ]
#     call_names = 'P'
#     shared_constraints = points < 17


class RaiseAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = [
        LastBidWas(positions.RHO, 'P'),
        RaiseOfPartnersLastSuit(),
        NotJumpFromLastContract()
    ]
    # Min: 1C X 1D P 2D, Max: 2S X P 3H P 4H
    # FIXME: Game doesn't seem like a raise here?
    constraints = {
        (      '3C', '4C'): (NO_CONSTRAINTS, rebids_after_takeout_double.MinorRaise),
        ('2D', '3D', '4D'): (NO_CONSTRAINTS, rebids_after_takeout_double.MinorRaise),
        ('2H', '3H', '4H'): (NO_CONSTRAINTS, rebids_after_takeout_double.MajorRaise),
        ('2S', '3S'      ): (NO_CONSTRAINTS, rebids_after_takeout_double.MajorRaise),
    }
    shared_constraints = MinLength(4)


# class JumpRaiseAfterTakeoutDouble(RebidAfterTakeoutDouble):
#     preconditions = [
#         RaiseOfPartnersLastSuit(),
#         JumpFromPartnerLastBid(exact_size=1)
#     ]
#     # Min: 1C X 1D P 3D, Max: 2S X P 3D P 5D
#     # FIXME: Game doesn't seem like a raise here?
#     constraints = {
#         (      '3C', '4C', '5C'): (NO_CONSTRAINTS, rebids_after_takeout_double.MinorRaise),
#         ('2D', '3D', '4D', '5D'): (NO_CONSTRAINTS, rebids_after_takeout_double.MinorRaise),
#         ('2H', '3H', '4H'      ): (NO_CONSTRAINTS, rebids_after_takeout_double.MajorRaise),
#         ('2S', '3S', '4H'      ): (NO_CONSTRAINTS, rebids_after_takeout_double.MajorRaise),
#     }
#     call_names = suit_bids_below_game('3D')
#     shared_constraints = [MinLength(4), points >= 19]
#     priority = rebids_after_takeout_double.JumpRaiseAfterTakeoutDouble


# class NewSuitAfterTakeoutDouble(RebidAfterTakeoutDouble):
#     preconditions = [
#         UnbidSuit(),
#         NotJumpFromLastContract()
#     ]
#     # Min: 1C X XX P 1D, Max: 2D X P 2S 3H
#     call_names = suit_bids_below_game('1D')
#     constraints = {
#         (      '2C', '3C'): (NO_CONSTRAINTS, rebids_after_takeout_double.ClubsNewSuit),
#         ('1D', '2D', '3D'): (NO_CONSTRAINTS, rebids_after_takeout_double.DiamondsNewSuit),
#         ('1H', '2H', '3H'): (NO_CONSTRAINTS, rebids_after_takeout_double.HeartsNewSuit),
#         ('1S', '2S'      ): (NO_CONSTRAINTS, rebids_after_takeout_double.SpadesNewSuit),
#     }
#     shared_constraints = MinLength(5)


# class JumpNewSuitAfterTakeoutDouble(RebidAfterTakeoutDouble):
#     preconditions = [
#         UnbidSuit(),
#         JumpFromLastContract(exact_size=1)
#     ]
#     # Min: 1C X 1D P 2H
#     call_names = suit_bids_below_game('2H')
#     shared_constraints = [MinLength(6), TwoOfTheTopThree(), points >= 21]
#     priority = rebids_after_takeout_double.JumpNewSuitAfterTakeoutDouble


class NotrumpAfterTakeoutDouble(RebidAfterTakeoutDouble):
    constraints = {
        '1N': (points >= 18, rebids_after_takeout_double.OneNotrumpAfterTakeoutDouble),
        # 2N depends on whether it is a jump.
        '3N': (points >= 22, rebids_after_takeout_double.ThreeNotrumpAfterTakeoutDouble), # FIXME: Techincally means 9+ tricks.
    }
    shared_constraints = StoppersInOpponentsSuits()


class NonJumpTwoNotrumpAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = NotJumpFromLastContract()
    call_names = '2N'
    shared_constraints = [points >= 19, StoppersInOpponentsSuits()]
    priority = rebids_after_takeout_double.TwoNotrumpAfterTakeoutDouble


class JumpTwoNotrumpAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = JumpFromLastContract()
    call_names = '2N'
    shared_constraints = [points >= 21, StoppersInOpponentsSuits()]
    priority = rebids_after_takeout_double.TwoNotrumpAfterTakeoutDouble


# class CueBidAfterTakeoutDouble(RebidAfterTakeoutDouble):
#     preconditions = [
#         NotJumpFromLastContract(),
#         CueBid(positions.RHO),
#     ]
#     # Min: 1C X 1D P 2C
#     call_names = suit_bids_below_game('2C')
#     shared_constraints = points >= 21
#     priority = rebids_after_takeout_double.CueBidAfterTakeoutDouble


# class TakeoutDoubleAfterTakeoutDouble(RebidAfterTakeoutDouble):
#     call_names = 'X'


preempt_priorities = enum.Enum(
    "EightCardPreempt",
    "SevenCardPreempt",
    "SixCardPreempt",
)
rule_order.order(*reversed(preempt_priorities))


class PreemptiveOpen(Opening):
    annotations = annotations.Preemptive
    # Never worth preempting in 4th seat.
    preconditions = InvertedPrecondition(LastBidWas(positions.LHO, 'P'))
    constraints = {
        # 3C only promises 6 cards due to 2C being taken for strong bids.
        (      '2D', '2H', '2S', '3C'): (MinLength(6), preempt_priorities.SixCardPreempt),
        (      '3D', '3H', '3S'): (MinLength(7), preempt_priorities.SevenCardPreempt),
        ('4C', '4D', '4H', '4S'): (MinLength(8), preempt_priorities.EightCardPreempt),
    }
    shared_constraints = [ThreeOfTheTopFiveOrBetter(), points >= 5]


class PreemptiveOvercall(DirectOvercall):
    annotations = annotations.Preemptive
    preconditions = [JumpFromLastContract(), UnbidSuit()]
    constraints = {
        ('2C', '2D', '2H', '2S'): (MinLength(6), overcall_priorities.TwoLevelPremptive),
        ('3C', '3D', '3H', '3S'): (MinLength(7), overcall_priorities.ThreeLevelPremptive),
        ('4C', '4D', '4H', '4S'): (MinLength(8), overcall_priorities.FourLevelPremptive),
    }
    conditional_priorities_per_call = {
        ('2C', '2D', '2H', '2S'): [(points <= 11, overcall_priorities.WeakTwoLevelPremptive)],
        ('3C', '3D', '3H', '3S'): [(points <= 11, overcall_priorities.WeakThreeLevelPremptive)],
        ('4C', '4D', '4H', '4S'): [(points <= 11, overcall_priorities.WeakFourLevelPremptive)],
    }
    shared_constraints = [ThreeOfTheTopFiveOrBetter(), points >= 5]


class ResponseToPreempt(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Preemptive)


class NewSuitResponseToPreempt(ResponseToPreempt):
    preconditions = [
        UnbidSuit(),
        NotJumpFromLastContract()
    ]
    call_names = [
              '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
        '4C', '4D',
    ]
    shared_constraints = [MinLength(5), MinCombinedPointsForPartnerMinimumSuitedRebid()]


the_law_priorities = enum.Enum(
    "FiveLevelLaw",
    "FourLevelLaw",
    "ThreeLevelLaw",
    "TwoLevelLaw",
)
rule_order.order(*reversed(the_law_priorities))


class LawOfTotalTricks(Rule):
    preconditions = [
        InvertedPrecondition(Opened(positions.Me)),
        RaiseOfPartnersLastSuit()
    ]
    shared_constraints = LengthSatisfiesLawOfTotalTricks()
    category = categories.LawOfTotalTricks
    constraints = {
        ('2C', '2D', '2H', '2S'): (NO_CONSTRAINTS, the_law_priorities.TwoLevelLaw),
        ('3C', '3D', '3H', '3S'): (NO_CONSTRAINTS, the_law_priorities.ThreeLevelLaw),
        ('4C', '4D', '4H', '4S'): (NO_CONSTRAINTS, the_law_priorities.FourLevelLaw),
        ('5C', '5D',           ): (NO_CONSTRAINTS, the_law_priorities.FiveLevelLaw),
    }


feature_asking_priorities = enum.Enum(
    "Gerber",
    "Blackwood",
)
rule_order.order(*reversed(feature_asking_priorities))

feature_response_priorities = enum.Enum(
    "Gerber",
    "Blackwood",
    "TwoNotrumpFeatureResponse",
)

class Gerber(Rule):
    category = categories.Gadget
    requires_planning = True
    shared_constraints = NO_CONSTRAINTS
    annotations = annotations.Gerber
    priority = feature_asking_priorities.Gerber


class GerberForAces(Gerber):
    call_names = '4C'
    preconditions = [
        LastBidHasStrain(positions.Partner, suit.NOTRUMP),
        InvertedPrecondition(LastBidHasAnnotation(positions.Partner, annotations.Artificial))
    ]


class GerberForKings(Gerber):
    call_names = '5C'
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Gerber)


class ResponseToGerber(Rule):
    category = categories.Relay
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.Gerber),
        NotJumpFromPartnerLastBid(),
    ]
    constraints = {
        '4D': z3.Or(number_of_aces == 0, number_of_aces == 4),
        '4H': number_of_aces == 1,
        '4S': number_of_aces == 2,
        '4N': number_of_aces == 3,
        '5D': z3.Or(number_of_kings == 0, number_of_kings == 4),
        '5H': number_of_kings == 1,
        '5S': number_of_kings == 2,
        '5N': number_of_kings == 3,
    }
    priority = feature_response_priorities.Gerber
    annotations = annotations.Artificial


class Blackwood(Rule):
    category = categories.Gadget
    requires_planning = True
    shared_constraints = NO_CONSTRAINTS
    annotations = annotations.Blackwood
    priority = feature_asking_priorities.Blackwood


class BlackwoodForAces(Blackwood):
    call_names = '4N'
    preconditions = [
        InvertedPrecondition(LastBidHasStrain(positions.Partner, suit.NOTRUMP)),
        EitherPrecondition(JumpFromLastContract(), HaveFit())
    ]


class BlackwoodForKings(Blackwood):
    call_names = '5N'
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Blackwood)


class ResponseToBlackwood(Rule):
    category = categories.Relay
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.Blackwood),
        NotJumpFromPartnerLastBid(),
    ]
    constraints = {
        '5C': z3.Or(number_of_aces == 0, number_of_aces == 4),
        '5D': number_of_aces == 1,
        '5H': number_of_aces == 2,
        '5S': number_of_aces == 3,
        '6C': z3.Or(number_of_kings == 0, number_of_kings == 4),
        '6D': number_of_kings == 1,
        '6H': number_of_kings == 2,
        '6S': number_of_kings == 3,
    }
    priority = feature_response_priorities.Blackwood
    annotations = annotations.Artificial


class TwoNotrumpFeatureRequest(ResponseToPreempt):
    category = categories.Gadget
    annotations = annotations.FeatureRequest
    requires_planning = True
    constraints = { '2N': MinimumCombinedPoints(22) }


class ResponseToTwoNotrumpFeatureRequest(Rule):
    category = categories.Gadget
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.FeatureRequest)
    priority = feature_response_priorities.TwoNotrumpFeatureResponse


class FeatureResponseToTwoNotrumpFeatureRequest(ResponseToTwoNotrumpFeatureRequest):
    preconditions = InvertedPrecondition(RebidSameSuit())
    annotations = annotations.Artificial
    call_names = ('3C', '3D', '3H', '3S')
    # Note: We could have a protected outside honor with as few as 6 points,
    # (QJTxxx in our main suit + Qxx in our outside honor suit)
    # Unittests would suggest we should require 9+?
    shared_constraints = [points >= 9, ThirdRoundStopper()]



class DefaultPass(Rule):
    preconditions = [InvertedPrecondition(ForcedToBid())]
    call_names = 'P'
    shared_constraints = NO_CONSTRAINTS
    category = categories.DefaultPass


# FIXME: This is wrong as soon as we try to support more than one system.
def _get_subclasses(base_class):
    subclasses = base_class.__subclasses__()
    for subclass in list(subclasses):
        subclasses.extend(_get_subclasses(subclass))
    return subclasses

def _concrete_rule_classes():
    return filter(lambda cls: not cls.__subclasses__(), _get_subclasses(Rule))


class StandardAmericanYellowCard(object):
    # Rule ordering does not matter.  We could have python crawl the files to generate this list instead.
    rules = [RuleCompiler.compile(description_class) for description_class in _concrete_rule_classes()]
    priority_ordering = rule_order

    rule_order.order(response_priorities, relay_priorities)
    rule_order.order(response_priorities, feature_response_priorities)
    rule_order.order(response_priorities, relay_priorities)
    rule_order.order(preempt_priorities, opening_priorities)
    rule_order.order(natural_priorities, preempt_priorities)
    rule_order.order(response_priorities, two_clubs_response_priorities)
    rule_order.order(response_priorities, jacoby_2n_response_priorities)
    rule_order.order(natural_priorities, overcall_priorities)
    rule_order.order(natural_priorities, response_priorities)
    rule_order.order(natural_priorities, opener_rebid_priorities)
    rule_order.order(natural_games, nt_response_priorities, natural_slams)
    rule_order.order(natural_priorities, stayman_response_priorities)
    rule_order.order(natural_priorities, GarbagePassStaymanRebid)
    rule_order.order(natural_priorities, two_clubs_opener_rebid_priorities)
    rule_order.order(natural_priorities, responder_rebid_priorities)
    rule_order.order(
        natural_priorities.ThreeLevelNaturalNT,
        stayman_rebid_priorities.GameForcingOtherMajor,
        natural_priorities.FourLevelNaturalMajor,
    )
    rule_order.order(natural_nt_part_scores, stayman_rebid_priorities.InvitationalOtherMajor, natural_suited_part_scores)
    rule_order.order(takeout_double_responses, natural_priorities)
    rule_order.order(ForcedRebidOriginalSuitByOpener, natural_priorities)
    rule_order.order(the_law_priorities, responder_rebid_priorities)
    rule_order.order(the_law_priorities, natural_priorities)
    rule_order.order(natural_priorities, NewSuitResponseToStandardOvercall, CuebidResponseToStandardOvercall)
    rule_order.order(RaiseResponseToStandardOvercall, the_law_priorities, NewSuitResponseToStandardOvercall, CuebidResponseToStandardOvercall)
    rule_order.order(DefaultPass, RaiseResponseToStandardOvercall)
    rule_order.order(sign_off_priorities, the_law_priorities)
    rule_order.order(DefaultPass, the_law_priorities)
    rule_order.order(DefaultPass, sign_off_priorities)
    rule_order.order(DefaultPass, opening_priorities)
    rule_order.order(natural_priorities, RaiseAfterTakeoutDouble)
    rule_order.order(SecondNegative, natural_priorities)
    rule_order.order(DefaultPass, rebids_after_takeout_double)
