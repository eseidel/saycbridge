# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.call import Call
from core.callexplorer import CallExplorer
from itertools import chain
from third_party import enum
from third_party.memoized import memoized
from z3b.constraints import *
from z3b.model import *
from z3b.orderings import PartialOrdering
from z3b.preconditions import *


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
    def __init__(self, rule, preconditions, known_calls, shared_constraints, annotations):
        self.dsl_rule = rule
        self.preconditions = preconditions
        self.known_calls = known_calls
        self.shared_constraints = shared_constraints
        self._annotations = annotations

    def requires_planning(self, history):
        return self.dsl_rule.requires_planning

    def annotations(self, history):
        return self._annotations

    @property
    def name(self):
        return self.dsl_rule.name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "CompiledRule(%s)" % repr(self.dsl_rule)

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
        per_call_constraints, _ = self.dsl_rule.per_call_constraints_and_priority(call)
        if per_call_constraints:
            exprs.extend(RuleCompiler.exprs_from_constraints(per_call_constraints, history, call))
        exprs.extend(RuleCompiler.exprs_from_constraints(self.shared_constraints, history, call))
        return exprs

    def meaning_of(self, history, call):
        exprs = self._constraint_exprs_for_call(history, call)
        for condition, priority in self.dsl_rule.conditional_priorities:
            condition_exprs = RuleCompiler.exprs_from_constraints(condition, history, call)
            yield priority, z3.And(exprs + condition_exprs)

        _, priority = self.dsl_rule.per_call_constraints_and_priority(call)
        assert priority
        yield priority, z3.And(exprs)


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
    def _collect_from_ancestors(cls, dls_class, property_name):
        getter = lambda ancestor: getattr(ancestor, property_name, [])
        # The DSL expects that parent preconditions, etc. apply before child ones.
        return map(getter, reversed(dls_class.__mro__))

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
    def _compile_known_calls(cls, dsl_class):
        if dsl_class.call_names:
            call_names = cls._ensure_list(dsl_class.call_names)
        else:
            call_names = dsl_class.constraints.keys()
        assert call_names, "%s: call_names or constraints map is required." % dsl_class.__name__
        return map(Call.from_string, call_names)

    @classmethod
    def compile(cls, dsl_rule_class):
        dsl_rule = dsl_rule_class()
        # Unclear if compiled results should be memoized on the rule?
        return CompiledRule(dsl_rule,
            known_calls=cls._compile_known_calls(dsl_rule_class),
            annotations=cls._joined_list_from_ancestors(dsl_rule_class, 'annotations'),
            preconditions=cls._joined_list_from_ancestors(dsl_rule_class, 'preconditions'),
            shared_constraints=cls._joined_list_from_ancestors(dsl_rule_class, 'shared_constraints')
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
    priority = None

    def __init__(self):
        assert self.priority or self.constraints, "" + self.name + " is missing priority"
        # Rules have to apply some constraints to the hand.
        assert self.constraints or self.shared_constraints, "" + self.name + " is missing constraints"
        # conditional_priorities doesn't work with self.constraints
        assert not self.conditional_priorities or not self.constraints
        assert not self.conditional_priorities or self.call_names

    @property
    def name(self):
        return self.__class__.__name__

    def __repr__(self):
        return "%s()" % self.name

    # constraints accepts various forms including:
    # constraints = { '1H': hearts > 5 }
    # constraints = { '1H': (hearts > 5, priority) }

    # FIXME: Should we split this into two methods? on for priority and one for constraints?
    def per_call_constraints_and_priority(self, call):
        constraints_tuple = self.constraints.get(call.name)
        if constraints_tuple:
            try:
                if isinstance(list(constraints_tuple)[-1], enum.EnumValue):
                    assert len(constraints_tuple) == 2
                    return constraints_tuple
            except TypeError:
                pass
        assert self.priority, "" + self.name + " is missing priority"
        return constraints_tuple, self.priority


relay_priorities = enum.Enum(
    "Relay",
)


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


class Natural(Rule):
    # FIXME: This should have a SomeoneOpened() precondition.
    category = categories.Natural


class SuitedToPlay(Natural):
    preconditions = [
        MinimumCombinedPointsPrecondition(12),
        PartnerHasAtLeastLengthInSuit(1)
    ]
    constraints = {
        '2C': (MinimumCombinedPoints(19), natural_priorities.TwoLevelNaturalMinor),
        '2D': (MinimumCombinedPoints(19), natural_priorities.TwoLevelNaturalMinor),
        '2H': (MinimumCombinedPoints(19), natural_priorities.TwoLevelNaturalMajor),
        '2S': (MinimumCombinedPoints(19), natural_priorities.TwoLevelNaturalMajor),

        '3C': (MinimumCombinedPoints(22), natural_priorities.ThreeLevelNaturalMinor),
        '3D': (MinimumCombinedPoints(22), natural_priorities.ThreeLevelNaturalMinor),
        '3H': (MinimumCombinedPoints(22), natural_priorities.ThreeLevelNaturalMajor),
        '3S': (MinimumCombinedPoints(22), natural_priorities.ThreeLevelNaturalMajor),

        '4C': (MinimumCombinedPoints(25), natural_priorities.FourLevelNaturalMinor),
        '4D': (MinimumCombinedPoints(25), natural_priorities.FourLevelNaturalMinor),
        '4H': (MinimumCombinedPoints(25), natural_priorities.FourLevelNaturalMajor),
        '4S': (MinimumCombinedPoints(25), natural_priorities.FourLevelNaturalMajor),

        '5C': (MinimumCombinedPoints(28), natural_priorities.FiveLevelNaturalMinor),
        '5D': (MinimumCombinedPoints(28), natural_priorities.FiveLevelNaturalMinor),
        '5H': (MinimumCombinedPoints(28), natural_priorities.FiveLevelNaturalMajor),
        '5S': (MinimumCombinedPoints(28), natural_priorities.FiveLevelNaturalMajor),

        '6C': (MinimumCombinedPoints(33), natural_priorities.SixLevelNaturalMinor),
        '6D': (MinimumCombinedPoints(33), natural_priorities.SixLevelNaturalMinor),
        '6H': (MinimumCombinedPoints(33), natural_priorities.SixLevelNaturalMajor),
        '6S': (MinimumCombinedPoints(33), natural_priorities.SixLevelNaturalMajor),

        '7C': (MinimumCombinedPoints(37), natural_priorities.SevenLevelNaturalMinor),
        '7D': (MinimumCombinedPoints(37), natural_priorities.SevenLevelNaturalMinor),
        '7H': (MinimumCombinedPoints(37), natural_priorities.SevenLevelNaturalMajor),
        '7S': (MinimumCombinedPoints(37), natural_priorities.SevenLevelNaturalMajor),
    }
    shared_constraints = [MinimumCombinedLength(8)]


class NotrumpToPlay(Natural):
    constraints = {
        '1N': [MinimumCombinedPoints(19), natural_priorities.OneLevelNaturalNT],
        '2N': [MinimumCombinedPoints(22), natural_priorities.TwoLevelNaturalNT],
        '3N': [MinimumCombinedPoints(25), natural_priorities.ThreeLevelNaturalNT],
        '4N': [MinimumCombinedPoints(28), natural_priorities.FourLevelNaturalNT],
        '5N': [MinimumCombinedPoints(31), natural_priorities.FiveLevelNaturalNT],
        '6N': [MinimumCombinedPoints(34), natural_priorities.SixLevelNaturalNT],
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


class Opening(Rule):
    annotations = annotations.Opening
    preconditions = NoOpening()



class OneClubOpening(Opening):
    call_names = '1C'
    shared_constraints = [OpeningRuleConstraint(), clubs >= 3]
    conditional_priorities = [
        (z3.Or(clubs > diamonds, z3.And(clubs == 3, diamonds == 3)), opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.LowerMinor


class OneDiamondOpening(Opening):
    call_names = '1D'
    shared_constraints = [OpeningRuleConstraint(), diamonds >= 3]
    conditional_priorities = [
        (diamonds > clubs, opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.HigherMinor


class OneHeartOpening(Opening):
    call_names = '1H'
    shared_constraints = [OpeningRuleConstraint(), hearts >= 5]
    conditional_priorities = [
        (hearts > spades, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.LowerMajor


class OneSpadeOpening(Opening):
    call_names = '1S'
    shared_constraints = [OpeningRuleConstraint(), spades >= 5]
    conditional_priorities = [
        (spades > hearts, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.HigherMajor


class NoTrumpOpening(Opening):
    annotations = annotations.NoTrumpSystemsOn
    constraints = {
        '1N': z3.And(points >= 15, points <= 17, balanced),
        '2N': z3.And(points >= 20, points <= 21, balanced)
    }
    priority = opening_priorities.NoTrumpOpening


# class OneNoTrumpOpening(Opening):
#     call_names = '1N'
#     shared_constraints =


# class TwoNoTrumpOpening(Opening):
#     annotations = annotations.NoTrumpSystemsOn
#     call_names = '2N'
#     shared_constraints = [points >= 20, points <= 21, balanced]
#     priority = opening_priorities.NoTrumpOpening


class StrongTwoClubs(Opening):
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


class Response(Rule):
    preconditions = [LastBidHasAnnotation(positions.Partner, annotations.Opening)]


class ResponseToOneLevelSuitedOpen(Response):
    preconditions = [
        LastBidHasLevel(positions.Partner, 1),
        InvertedPrecondition(LastBidHasStrain(positions.Partner, suit.NOTRUMP))
    ]


class OneDiamondResponse(ResponseToOneLevelSuitedOpen):
    call_names = '1D'
    shared_constraints = [points >= 6, diamonds >= 4]
    priority = response_priorities.OneDiamondResponse


class OneHeartResponse(ResponseToOneLevelSuitedOpen):
    call_names = '1H'
    shared_constraints = [points >= 6, hearts >= 4]
    conditional_priorities = [
        (z3.And(hearts >= 5, hearts > spades), response_priorities.LongestNewMajor),
        (hearts >= 5, response_priorities.OneHeartWithFiveResponse),
    ]
    priority = response_priorities.OneHeartWithFourResponse


class OneSpadeResponse(ResponseToOneLevelSuitedOpen):
    call_names = '1S'
    shared_constraints = [points >= 6, spades >= 4]
    conditional_priorities = [
        (spades >= 5, response_priorities.OneSpadeWithFiveResponse)
    ]
    priority = response_priorities.OneSpadeWithFourResponse


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
    annotations = [annotations.Jacoby2N, annotations.Artificial]


jacoby_2n_response_priorities = enum.Enum(
    # Currently favoring features over slam interest.  Unclear if that's correct?
    "SolidSuit",
    "Singleton",
    "Slam",
    "Notrump",
    "MinimumGame",
)


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
    shared_constraints = [MinLength(5), ThreeOfTheTopFive()]
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


class NegativeDouble(ResponseToOneLevelSuitedOpen):
    call_names = 'X'
    preconditions = [
        LastBidHasSuit(positions.RHO),
        MaxLevel(2),
    ]
    priority = response_priorities.NegativeDouble
    annotations = [annotations.NegativeDouble, annotations.Artificial]


class NegativeDoubleOfOneDiamondOverOneClub(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '1D'),
        LastBidWas(positions.Partner, '1C'),
    ]
    shared_constraints = [points >= 6, hearts >= 4, spades >= 4]


class NegativeDoubleOfOneHeartOverOneClub(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '1H'),
        LastBidWas(positions.Partner, '1C'),
    ]
    shared_constraints = [points >= 6, spades == 4]


class NegativeDoubleOfOneSpadeOverOneClub(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '1S'),
        LastBidWas(positions.Partner, '1C'),
    ]
    shared_constraints = [points >= 6, diamonds >= 3, hearts >= 4]


class NegativeDoubleOfTwoDiamondsOverOneClub(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2D'),
        LastBidWas(positions.Partner, '1C'),
    ]
    shared_constraints = [points >= 8, hearts >= 4, spades >= 4]


class NegativeDoubleOfTwoHeartsOverOneClub(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2H'),
        LastBidWas(positions.Partner, '1C'),
    ]
    shared_constraints = [points >= 8, diamonds >= 3, spades >= 4]


class NegativeDoubleOfTwoSpadesOverOneClub(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2S'),
        LastBidWas(positions.Partner, '1C'),
    ]
    shared_constraints = [points >= 8, diamonds >= 3, hearts >= 4]


class NegativeDoubleOfOneHeartOverOneDiamond(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '1H'),
        LastBidWas(positions.Partner, '1D'),
    ]
    shared_constraints = [points >= 6, spades == 4]


class NegativeDoubleOfOneSpadeOverOneDiamond(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '1S'),
        LastBidWas(positions.Partner, '1D'),
    ]
    shared_constraints = [points >= 6, clubs >= 3, hearts >= 4]


class NegativeDoubleOfTwoClubsOverOneDiamond(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2C'),
        LastBidWas(positions.Partner, '1D'),
    ]
    shared_constraints = [points >= 8, hearts >= 4, spades >= 4]


class NegativeDoubleOfTwoHeartsOverOneDiamond(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2H'),
        LastBidWas(positions.Partner, '1D'),
    ]
    shared_constraints = [points >= 8, clubs >= 3, spades >= 4]


class NegativeDoubleOfTwoSpadesOverOneDiamond(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2S'),
        LastBidWas(positions.Partner, '1D'),
    ]
    shared_constraints = [points >= 8, clubs >= 3, hearts >= 4]


class NegativeDoubleOfOneSpadeOverOneHeart(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '1S'),
        LastBidWas(positions.Partner, '1H'),
    ]
    shared_constraints = [points >= 6, clubs >= 3, diamonds >= 3]


class NegativeDoubleOfTwoClubsOverOneHeart(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2C'),
        LastBidWas(positions.Partner, '1H'),
    ]
    shared_constraints = [points >= 8, diamonds >= 3, spades >= 4]


class NegativeDoubleOfTwoDiamondsOverOneHeart(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2D'),
        LastBidWas(positions.Partner, '1H'),
    ]
    shared_constraints = [points >= 8, clubs >= 3, spades >= 4]


class NegativeDoubleOfTwoSpadesOverOneHeart(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2S'),
        LastBidWas(positions.Partner, '1H'),
    ]
    shared_constraints = [points >= 8, clubs >= 3, diamonds >= 3]


class NegativeDoubleOfTwoClubsOverOneSpade(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2C'),
        LastBidWas(positions.Partner, '1S'),
    ]
    shared_constraints = [points >= 8, diamonds >= 3, hearts >= 4]


class NegativeDoubleOfTwoDiamondsOverOneSpades(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2D'),
        LastBidWas(positions.Partner, '1S'),
    ]
    shared_constraints = [points >= 8, clubs >= 3, hearts >= 4]


class NegativeDoubleOfTwoHeartsOverOneSpade(NegativeDouble):
    preconditions = [
        LastBidWas(positions.RHO, '2H'),
        LastBidWas(positions.Partner, '1S'),
    ]
    shared_constraints = [points >= 8, clubs >= 3, diamonds >= 3]


two_clubs_response_priorities = enum.Enum(
    "SuitResponse",
    "NoBiddableSuit",
    "WaitingResponse",
)


class ResponseToStrongTwoClubs(Response):
    preconditions = LastBidWas(positions.Partner, '2C')


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
    "JumpShiftByOpener",
    # FIXME: 1S P 2D looks like this will will prefer 3C over 2S!
    "NewSuitClubs",
    "NewSuitDiamonds",
    "NewSuitHearts",
    "NewSuitSpades",
    "ReverseDiamonds",
    "ReverseHearts",
    "ReverseSpades",
    "UnforcedRebidOriginalSuit",
    "RebidOneNotrump",
    "ForcedRebidOriginalSuit",
)


forced_rebid_priorities = enum.Enum(
    "ForcedRebidOriginalSuit",
)

class OpenerRebid(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Opening)


class RebidAfterOneLevelOpen(OpenerRebid):
    preconditions = LastBidHasLevel(positions.Me, 1)


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


class NewSuitByOpener(RebidAfterOneLevelOpen):
    preconditions = [
        # FIXME: MyLastBidWasOneOfASuit(),
        SuitLowerThanMyLastSuit(),
        NotJumpFromLastContract(),
        UnbidSuit(),
    ]
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


class ReverseByOpener(RebidAfterOneLevelOpen):
    preconditions = [
        InvertedPrecondition(SuitLowerThanMyLastSuit()),
        UnbidSuit(),
        NotJumpFromLastContract(),
    ]
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


class SupportPartnerSuit(OpenerRebid):
    preconditions = [
        InvertedPrecondition(RebidSameSuit()),
        RaiseOfPartnersLastSuit(),
    ]


class SupportPartnerMajorSuit(SupportPartnerSuit):
    constraints = {
        '2H': (NO_CONSTRAINTS, opener_rebid_priorities.SupportMajorMin),
        '2S': (NO_CONSTRAINTS, opener_rebid_priorities.SupportMajorMin),

        '3H': (MinimumCombinedPoints(22), opener_rebid_priorities.SupportMajorLimit),
        '3S': (MinimumCombinedPoints(22), opener_rebid_priorities.SupportMajorLimit),

        '4H': (MinimumCombinedPoints(25), opener_rebid_priorities.SupportMajorMax),
        '4S': (MinimumCombinedPoints(25), opener_rebid_priorities.SupportMajorMax),
    }
    shared_constraints = MinimumCombinedLength(8)


class RebidOriginalSuitByOpener(RebidAfterOneLevelOpen):
    preconditions = [
        LastBidHasLevel(positions.Me, 1),
        RebidSameSuit(),
        NotJumpFromLastContract(),
    ]


class UnforcedRebidOriginalSuitByOpener(RebidOriginalSuitByOpener):
    preconditions = InvertedPrecondition(ForcedToBid())
    call_names = ['2C', '2D', '2H', '2S']
    shared_constraints = MinLength(6)
    priority = opener_rebid_priorities.UnforcedRebidOriginalSuit


class ForcedRebidOriginalSuitByOpener(RebidOriginalSuitByOpener):
    preconditions = ForcedToBid()
    call_names = ['2C', '2D', '2H', '2S']
    conditional_priorities = [
        (MinLength(6), opener_rebid_priorities.UnforcedRebidOriginalSuit),
    ]
    shared_constraints = MinLength(5)
    priority = forced_rebid_priorities.ForcedRebidOriginalSuit


class JumpShiftByOpener(RebidAfterOneLevelOpen):
    preconditions = JumpShift.preconditions
    # The lowest possible jumpshift is 1C P 1D P 2H.
    # The highest possible jumpshift is 1S P 2H P 4D
    call_names = ['2H', '2S', '3C', '3D', '3H', '3S', '4C', '4D']
    # FIXME: The book mentions that opener jumpshifts don't always promise 4, especially for 1C P MAJOR P 3D
    shared_constraints = (points >= 19, MinLength(4))
    priority = opener_rebid_priorities.JumpShiftByOpener


two_clubs_opener_rebid_priorities = enum.Enum(
    "SuitedJumpRebid",
    "SuitedRebid",
)


class OpenerRebidAfterStrongTwoClubs(OpenerRebid):
    preconditions = LastBidWas(positions.Me, '2C')


class OpenerSuitedRebidAfterStrongTwoClubs(OpenerRebidAfterStrongTwoClubs):
    preconditions = [UnbidSuit(), NotJumpFromLastContract()]
    # This maxes out at 4C -> 2C P 3D P 4C
    # If the opponents are competing we're just gonna double them anyway.
    call_names = ['2H', '2S', '3C', '3D', '3H', '3S', '4C']
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


# FIXME: We should add an OpenerRebid of 3N over 2C P 2N P to show a minimum 22-24 HCP
# instead of jumping to 5N which just wastes bidding space.
# This is not covered in the book or the SAYC pdf.


# class ResponderRebid(Rule):
#     preconditions = [
#         # FIXME: Specifically these only apply when 2 bids ago partner opened.
#         Opened(positions.Partner),
#         HaveBid(),
#         IsSuitedProtocol()
#     ]


# class SecondNegative(ResponderRebid):
#     preconditions = [
#         LastBidWas(positions.Me, '2D'),
#         InvertedPrecondition(ForcedToBid()), # Does not apply over 2C,2D,2N
#     ]
#     call_names = '3C'
#     shared_constraints = NO_CONSTRAINTS
#     annotations = annotations.Artificial


nt_response_priorities = enum.Enum(
    "LongMajorSlamInvitation",
    "NoTrumpJumpRaise",
    "NoTrumpMinimumRaise",
    "JacobyTransferToLongerMajor",
    "JacobyTransferToSpadesWithGameForcingValues",
    "JacobyTransferToHeartsWithGameForcingValues",
    "JacobyTransferToHearts",
    "JacobyTransferToSpades",
    "Stayman",
    "LongMinorGameInvitation",
    "TwoSpadesRelay",
    "GarbageStayman",
)


class NoTrumpResponse(Rule):
    category = categories.NoTrumpSystem
    preconditions = [
        # 1N overcalls have systems on too, partner does not have to have opened
        LastBidHasAnnotation(positions.Partner, annotations.NoTrumpSystemsOn),
    ]


class BasicStayman(NoTrumpResponse):
    annotations = [annotations.Artificial, annotations.Stayman]
    priority = nt_response_priorities.Stayman
    shared_constraints = [z3.Or(hearts >= 4, spades >= 4)]


class Stayman(BasicStayman):
    preconditions = NotJumpFromPartnerLastBid()
    constraints = {
        # FIXME: I think of GarbageStayman as guarenteeing support in any response.
        '2C': ConstraintOr(MinimumCombinedPoints(23), z3.And(spades <= 4, hearts <= 4, diamonds <= 5, clubs <= 1)),
        '3C': MinimumCombinedPoints(25),
    }


class StolenTwoClubStayman(BasicStayman):
    preconditions = LastBidWas(positions.RHO, '2C')
    constraints = { 'X': MinimumCombinedPoints(23) }


class StolenThreeClubStayman(BasicStayman):
    preconditions = LastBidWas(positions.RHO, '3C')
    constraints = { 'X': MinimumCombinedPoints(25) }


class NoTrumpTransferResponse(NoTrumpResponse):
    annotations = [annotations.Artificial, annotations.Transfer]


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
        '2S': diamonds >= 6 or clubs >= 6,
    }
    priority = nt_response_priorities.TwoSpadesRelay


class AcceptTransferToHearts(Rule):
    category = categories.Relay
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.Transfer),
        LastBidHasStrain(positions.Partner, suit.DIAMONDS),
        NotJumpFromPartnerLastBid(),
    ]
    call_names = ['2H', '4H']
    shared_constraints = NO_CONSTRAINTS
    priority = relay_priorities.Relay


class AcceptTransferToSpades(Rule):
    category = categories.Relay
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.Transfer),
        LastBidHasStrain(positions.Partner, suit.HEARTS),
        NotJumpFromPartnerLastBid(),
    ]
    call_names = ['2S', '4S']
    shared_constraints = NO_CONSTRAINTS
    priority = relay_priorities.Relay


stayman_response_priorities = enum.Enum(
    "HeartStaymanResponse",
    "SpadeStaymanResponse",
    "DiamondStaymanResponse",
    "PassStaymanResponse",
)


class StaymanResponse(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Stayman)
    category = categories.NoTrumpSystem


class NaturalStaymanResponse(StaymanResponse):
    preconditions = NotJumpFromPartnerLastBid()
    constraints = {
        '2H': (hearts >= 4, stayman_response_priorities.HeartStaymanResponse),
        '2S': (spades >= 4, stayman_response_priorities.SpadeStaymanResponse),
        '3H': (hearts >= 4, stayman_response_priorities.HeartStaymanResponse),
        '3S': (spades >= 4, stayman_response_priorities.SpadeStaymanResponse),
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


stayman_rebid_priorities = enum.Enum(
    "GarbagePassStaymanRebid",
)


class StaymanRebid(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Stayman)
    category = categories.NoTrumpSystem


class GarbagePassStaymanRebid(StaymanRebid):
    call_names = 'P'
    shared_constraints = [points <= 7]
    priority = stayman_rebid_priorities.GarbagePassStaymanRebid


overcall_priorities = enum.Enum(
    "MichaelsCuebid",
    "Unusual2N",
    "DirectOvercall1N",
    "TakeoutDouble",
    "DirectOvercallLongestMajor",
    "DirectOvercallMajor",
    "DirectOvercallLongestMinor",
    "DirectOvercallMinor",
    "FourLevelPremptive",
    "ThreeLevelPremptive",
    "TwoLevelPremptive",
)


class DirectOvercall(Rule):
    preconditions = [
        LastBidHasAnnotation(positions.RHO, annotations.Opening),
    ]


class StandardDirectOvercall(DirectOvercall):
    preconditions = [
        LastBidHasSuit(positions.RHO),
        NotJumpFromLastContract(),
        UnbidSuit(),
    ]


class OneDiamondOvercall(StandardDirectOvercall):
    call_names = '1D'
    shared_constraints = [MinLength(5), points >= 8]
    priority = overcall_priorities.DirectOvercallMinor


class OneHeartOvercall(StandardDirectOvercall):
    call_names = '1H'
    shared_constraints = [MinLength(5), points >= 8]
    conditional_priorities = [
        (hearts > spades, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class OneSpadeOvercall(StandardDirectOvercall):
    call_names = '1S'
    shared_constraints = [MinLength(5), points >= 8]
    conditional_priorities = [
        (spades >= hearts, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class TwoClubOvercall(StandardDirectOvercall):
    call_names = '2C'
    shared_constraints = [MinLength(5), points >= 10]
    conditional_priorities = [
        (clubs > diamonds, overcall_priorities.DirectOvercallLongestMinor),
    ]
    priority = overcall_priorities.DirectOvercallMinor


class TwoDiamondOvercall(StandardDirectOvercall):
    call_names = '2D'
    shared_constraints = [MinLength(5), points >= 10]
    conditional_priorities = [
        (diamonds >= clubs, overcall_priorities.DirectOvercallLongestMinor),
    ]
    priority = overcall_priorities.DirectOvercallMinor


class TwoHeartOvercall(StandardDirectOvercall):
    call_names = '2H'
    shared_constraints = [MinLength(5), points >= 10]
    conditional_priorities = [
        (hearts > spades, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class TwoSpadeOvercall(StandardDirectOvercall):
    call_names = '2S'
    shared_constraints = [MinLength(5), points >= 10]
    conditional_priorities = [
        (spades >= hearts, overcall_priorities.DirectOvercallLongestMajor),
    ]
    priority = overcall_priorities.DirectOvercallMajor


class DirectOvercall1N(DirectOvercall):
    call_names = '1N'
    shared_constraints = [points >= 15, points <= 17, balanced, StopperInRHOSuit()]
    priority = overcall_priorities.DirectOvercall1N
    annotations = annotations.NoTrumpSystemsOn


class MichaelsCuebid(DirectOvercall):
    preconditions = [
        NotJumpFromLastContract(),
        InvertedPrecondition(UnbidSuit()),
    ]
    constraints = {
        '2C': (z3.And(hearts >= 5, spades >= 5), overcall_priorities.MichaelsCuebid),
        '2D': (z3.And(hearts >= 5, spades >= 5), overcall_priorities.MichaelsCuebid),
        '2H': (z3.And(spades >= 5, z3.Or(clubs >= 5, diamonds >= 5)), overcall_priorities.MichaelsCuebid),
        '2S': (z3.And(hearts >= 5, z3.Or(clubs >= 5, diamonds >= 5)), overcall_priorities.MichaelsCuebid),
    }
    annotations = [annotations.MichaelsCuebid, annotations.Artificial]
    shared_constraints = [points >= 8]


class Unusual2N(DirectOvercall):
    preconditions = [
        JumpFromLastContract(),
    ]
    call_names = '2N'
    shared_constraints = [Unusual2NShape()]
    annotations = [annotations.Unusual2N, annotations.Artificial]
    priority = overcall_priorities.Unusual2N


class TakeoutDouble(Rule):
    call_names = 'X'
    preconditions = [
        LastBidHasSuit(),
        HasNotBid(positions.Partner),
        # LastBidWasNaturalSuit(),
        # LastBidWasBelowGame(),
        MinUnbidSuitCount(2),
    ]
    annotations = [annotations.TakeoutDouble, annotations.Artificial]
    shared_constraints = SupportForUnbidSuits()
    priority = overcall_priorities.TakeoutDouble


class OneLevelTakeoutDouble(TakeoutDouble):
    preconditions = MaxLevel(1)
    shared_constraints = points >= 11


preempt_priorities = enum.Enum(
    "FourLevelPremptive",
    "ThreeLevelPremptive",
    "TwoLevelPremptive",
)


class TwoLevelPremptiveOpen(Opening):
    call_names = ['2D', '2H', '2S']
    shared_constraints = [MinLength(6), ThreeOfTheTopFive(), points >= 5]
    priority = preempt_priorities.TwoLevelPremptive


class ThreeLevelPremptiveOpen(Opening):
    call_names = ['3C', '3D', '3H', '3S']
    shared_constraints = [MinLength(7), ThreeOfTheTopFive(), points >= 5]
    priority = preempt_priorities.ThreeLevelPremptive


class FourLevelPremptiveOpen(Opening):
    call_names = ['4C', '4D', '4H', '4S']
    shared_constraints = [MinLength(8), ThreeOfTheTopFive(), points >= 5]
    priority = preempt_priorities.FourLevelPremptive


class PreemptiveOvercall(DirectOvercall):
    preconditions = JumpFromLastContract()
    shared_constraints = [ThreeOfTheTopFive(), points >= 5]


# FIXME: Should we use conditional priorities instead of upper bounding the points?
class TwoLevelPremptiveOvercall(PreemptiveOvercall):
    call_names = ['2C', '2D', '2H', '2S']
    shared_constraints = MinLength(6)
    priority = overcall_priorities.TwoLevelPremptive


class ThreeLevelPremptiveOvercall(PreemptiveOvercall):
    call_names = ['3C', '3D', '3H', '3S']
    shared_constraints = MinLength(7)
    priority = overcall_priorities.ThreeLevelPremptive


class FourLevelPremptiveOvercall(PreemptiveOvercall):
    call_names = ['4C', '4D', '4H', '4S']
    shared_constraints = MinLength(8)
    priority = overcall_priorities.FourLevelPremptive


the_law_priorities = enum.Enum(
    "FiveLevelLaw",
    "FourLevelLaw",
    "ThreeLevelLaw",
    "TwoLevelLaw",
)


class LawOfTotalTricks(Rule):
    preconditions = [
        InvertedPrecondition(Opened(positions.Me)),
        RaiseOfPartnersLastSuit()
    ]
    shared_constraints = LengthSatisfiesLawOfTotalTricks()
    category = categories.LawOfTotalTricks


class TwoLevelLaw(LawOfTotalTricks):
    call_names = ['2C', '2D', '2H', '2S']
    priority = the_law_priorities.TwoLevelLaw


class ThreeLevelLaw(LawOfTotalTricks):
    call_names = ['3C', '3D', '3H', '3S']
    priority = the_law_priorities.ThreeLevelLaw


class FourLevelLaw(LawOfTotalTricks):
    call_names = ['4C', '4D', '4H', '4S']
    priority = the_law_priorities.FourLevelLaw


class FiveLevelLaw(LawOfTotalTricks):
    call_names = ['5C', '5D']
    priority = the_law_priorities.FiveLevelLaw


feature_asking_priorites = enum.Enum(
    "Gerber",
    "Blackwood",
)


class Gerber(Rule):
    category = categories.Gadget
    requires_planning = True
    shared_constraints = NO_CONSTRAINTS
    annotations = annotations.Gerber
    priority = feature_asking_priorites.Gerber


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
    priority = feature_asking_priorites.Gerber
    annotations = annotations.Artificial


# Blackwood is done, just needs JumpOrHaveFit() and some testing.
# class Blackwood(Rule):
#     category = categories.Gadget
#     requires_planning = True
#     shared_constraints = NO_CONSTRAINTS
#     annotations = annotations.Blackwood
#     priority = feature_asking_priorites.Blackwood


# class BlackwoodForAces(Blackwood):
#     call_names = '4N'
#     preconditions = [
#         InvertedPrecondition(LastBidHasStrain(positions.Partner, suit.NOTRUMP)),
#         InvertedPrecondition(LastBidHasAnnotation(positions.Partner, annotations.Artificial)),
#         JumpOrHaveFit()
#     ]


# class BlackwoodForKings(Blackwood):
#     call_names = '5N'
#     preconditions = LastBidHasAnnotation(positions.Me, annotations.Blackwood)


# class ResponseToBlackwood(Rule):
#     category = categories.Relay
#     preconditions = [
#         LastBidHasAnnotation(positions.Partner, annotations.Blackwood),
#         NotJumpFromPartnerLastBid(),
#     ]
#     constraints = {
#         '4C': z3.Or(number_of_aces == 0, number_of_aces == 4),
#         '4D': number_of_aces == 1,
#         '4H': number_of_aces == 2,
#         '4S': number_of_aces == 3,
#         '5C': z3.Or(number_of_kings == 0, number_of_kings == 4),
#         '5D': number_of_kings == 1,
#         '5H': number_of_kings == 2,
#         '5S': number_of_kings == 3,
#     }
#     priority = feature_asking_priorites.Blackwood
#     annotations = annotations.Artificial

pass_priorities = enum.Enum(
    "Default",
)

class DefaultPass(Rule):
    preconditions = [InvertedPrecondition(ForcedToBid())]
    call_names = 'P'
    shared_constraints = NO_CONSTRAINTS
    category = categories.DefaultPass
    priority = pass_priorities.Default


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
    priority_ordering = PartialOrdering()

    priority_ordering.make_less_than(response_priorities, relay_priorities)
    priority_ordering.make_less_than(preempt_priorities, opening_priorities)
    priority_ordering.make_less_than(natural_priorities, preempt_priorities)
    priority_ordering.make_less_than(response_priorities, nt_response_priorities)
    priority_ordering.make_less_than(response_priorities, two_clubs_response_priorities)
    priority_ordering.make_less_than(response_priorities, jacoby_2n_response_priorities)
    priority_ordering.make_less_than(natural_priorities, overcall_priorities)
    priority_ordering.make_less_than(natural_priorities, response_priorities)
    priority_ordering.make_less_than(natural_priorities, opener_rebid_priorities)
    priority_ordering.make_less_than(natural_priorities, nt_response_priorities)
    priority_ordering.make_less_than(natural_priorities, stayman_response_priorities)
    priority_ordering.make_less_than(natural_priorities, stayman_rebid_priorities)
    priority_ordering.make_less_than(natural_priorities, two_clubs_opener_rebid_priorities)
    priority_ordering.make_less_than(forced_rebid_priorities, natural_priorities)
    priority_ordering.make_less_than(the_law_priorities, natural_priorities)
    priority_ordering.make_less_than(pass_priorities, the_law_priorities)
    priority_ordering.make_less_than(pass_priorities, opening_priorities)

    priority_ordering.make_transitive()
