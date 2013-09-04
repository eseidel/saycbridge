# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b import enum
from z3b.constraints import *
from z3b.model import *
from z3b.natural import *
from z3b.preconditions import *
from z3b.rule_compiler import Rule, RuleCompiler, rule_order, categories


relay_priorities = enum.Enum(
    "SuperAccept",
    "Accept",
)
rule_order.order(*reversed(relay_priorities))


opening_priorities = enum.Enum(
    "StrongTwoClubs",
    "NotrumpOpening",
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


class NotrumpOpening(Opening):
    annotations = annotations.NotrumpSystemsOn
    constraints = {
        '1N': z3.And(points >= 15, points <= 17, balanced),
        '2N': z3.And(points >= 20, points <= 21, balanced)
    }
    priority = opening_priorities.NotrumpOpening


class StrongTwoClubs(Opening):
    annotations = annotations.StrongTwoClubOpening
    call_names = '2C'
    shared_constraints = points >= 22  # FIXME: Should support "or 9+ winners"
    priority = opening_priorities.StrongTwoClubs


class Response(Rule):
    preconditions = [LastBidHasAnnotation(positions.Partner, annotations.Opening)]


class ResponseToOneLevelSuitedOpen(Response):
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.OneLevelSuitOpening),
    ]


new_one_level_suit_responses = enum.Enum(
    "LongestNewMajor",
    "OneSpadeWithFive",
    "OneHeartWithFive",
    "OneDiamond",
    "OneHeartWithFour",
    "OneSpadeWithFour",
)
rule_order.order(*reversed(new_one_level_suit_responses))


new_one_level_major_responses = set([
    new_one_level_suit_responses.LongestNewMajor,
    new_one_level_suit_responses.OneSpadeWithFive,
    new_one_level_suit_responses.OneHeartWithFive,
    new_one_level_suit_responses.OneHeartWithFour,
    new_one_level_suit_responses.OneSpadeWithFour,
])

new_one_level_minor_responses = new_one_level_suit_responses.OneDiamond


class OneLevelNewSuitResponse(ResponseToOneLevelSuitedOpen):
    shared_constraints = points >= 6
    constraints = {
        '1D': (diamonds >= 4, new_one_level_suit_responses.OneDiamond),
        '1H': (hearts >= 4, new_one_level_suit_responses.OneHeartWithFour),
        '1S': (spades >= 4, new_one_level_suit_responses.OneSpadeWithFour),
    }
    # FIXME: 4 should probably be the special case and 5+ be the default priority.
    conditional_priorities_per_call = {
        '1H': [
            (z3.And(hearts >= 5, hearts > spades), new_one_level_suit_responses.LongestNewMajor),
            (hearts >= 5, new_one_level_suit_responses.OneHeartWithFive),
        ],
        '1S': [(spades >= 5, new_one_level_suit_responses.OneSpadeWithFive)]
    }


class OneNotrumpResponse(ResponseToOneLevelSuitedOpen):
    call_names = '1N'
    shared_constraints = points >= 6


class RaiseResponse(ResponseToOneLevelSuitedOpen):
    preconditions = [
        RaiseOfPartnersLastSuit(),
        LastBidHasAnnotation(positions.Partner, annotations.Opening)
    ]


raise_responses = enum.Enum(
    "MajorLimit",
    "MajorMinimum",

    "MinorLimit",
    "MinorMinimum",
)
rule_order.order(*reversed(raise_responses))


major_raise_responses = set([
    raise_responses.MajorLimit,
    raise_responses.MajorMinimum,
])


minor_raise_responses = set([
    raise_responses.MinorLimit,
    raise_responses.MinorMinimum,
])


minimum_raise_responses = set([
    raise_responses.MinorMinimum,
    raise_responses.MajorMinimum,
])


class MinimumRaise(RaiseResponse):
    priorities_per_call = {
        ('2C', '2D'): raise_responses.MinorMinimum,
        ('2H', '2S'): raise_responses.MajorMinimum,
    }
    shared_constraints = [MinimumCombinedLength(8), MinimumCombinedSupportPoints(18)]


class LimitRaise(RaiseResponse):
    preconditions = InvertedPrecondition(LastBidHasAnnotation(positions.RHO, annotations.TakeoutDouble))
    priorities_per_call = {
        ('3C', '3D'): raise_responses.MinorLimit,
        ('3H', '3S'): raise_responses.MajorLimit,
    }
    shared_constraints = [
        MinimumCombinedLength(8),
        # We shouldn't make a limit raise with less than 6 HCP\
        # even with a large number of support points.
        points >= 6,
        MinimumCombinedSupportPoints(22),
    ]

class MajorJumpToGame(RaiseResponse):
    call_names = ['4H', '4S']
    shared_constraints = [MinimumCombinedLength(10), points < 10]


class ThreeNotrumpMajorResponse(ResponseToOneLevelSuitedOpen):
    preconditions = LastBidHasStrain(positions.Partner, suit.MAJORS)
    call_names = '3N'
    # This is a very specific range per page 43.
    # With 27+ points, do we need to worry about stoppers in RHO's suit?
    shared_constraints = [balanced, points >= 15, points <= 17]


class NotrumpResponseToMinorOpen(ResponseToOneLevelSuitedOpen):
    preconditions = [
        LastBidHasStrain(positions.Partner, suit.MINORS),
        InvertedPrecondition(LastBidHasAnnotation(positions.RHO, annotations.TakeoutDouble)),
    ]
    constraints = {
        '2N': z3.And(points >= 13, points <= 15),
        '3N': z3.And(points >= 16, points >= 17),
    }
    shared_constraints = balanced


class Jordan(ResponseToOneLevelSuitedOpen):
    preconditions = LastBidHasAnnotation(positions.RHO, annotations.TakeoutDouble)
    call_names = '2N'
    shared_constraints = [
        MinimumCombinedLength(8, use_partners_last_suit=True),
        MinimumCombinedPoints(22),
    ]


class RedoubleResponseRHOTakeoutDouble(ResponseToOneLevelSuitedOpen):
    preconditions = LastBidHasAnnotation(positions.RHO, annotations.TakeoutDouble)
    call_names = 'XX'
    shared_constraints = MinimumCombinedPoints(22)


class JumpRaiseResponseToAfterRHOTakeoutDouble(RaiseResponse):
    preconditions = LastBidHasAnnotation(positions.RHO, annotations.TakeoutDouble)
    call_names = ['3C', '3D', '3H', '3S']
    shared_constraints = [MinimumCombinedLength(9)]


class JumpShift(object):
    preconditions = [UnbidSuit(), JumpFromLastContract(exact_size=1)]


class JumpShiftResponseToOpenAfterRHODouble(ResponseToOneLevelSuitedOpen):
    preconditions = JumpShift.preconditions + [
        LastBidHasAnnotation(positions.RHO, annotations.TakeoutDouble),
    ]
    call_names = ['2D', '2H', '2S', '3C', '3D', '3H']
    shared_constraints = [points >= 5, MinLength(6), TwoOfTheTopThree()]


defenses_against_takeout_double = [
    Jordan,
    RedoubleResponseRHOTakeoutDouble,
    JumpRaiseResponseToAfterRHOTakeoutDouble,
    JumpShiftResponseToOpenAfterRHODouble,
]
rule_order.order(*reversed(defenses_against_takeout_double))


# FIXME: We should bid longer suits when possible, up the line for 4 cards.
# we don't currently bid 2D over 2C when we have longer diamonds.
new_two_level_suit_responses = enum.Enum(
    "TwoClubs",
    "TwoDiamonds",
    "TwoHearts",
    "TwoSpades",
)
rule_order.order(*reversed(new_two_level_suit_responses))


new_two_level_minor_responses = set([
    new_two_level_suit_responses.TwoClubs,
    new_two_level_suit_responses.TwoDiamonds,
])


new_two_level_major_responses = set([
    new_two_level_suit_responses.TwoHearts,
    new_two_level_suit_responses.TwoSpades,
])


class NewSuitAtTheTwoLevel(ResponseToOneLevelSuitedOpen):
    preconditions = [UnbidSuit(), NotJumpFromLastContract()]
    constraints = {
        '2C' : (clubs >= 4, new_two_level_suit_responses.TwoClubs),
        '2D' : (diamonds >= 4, new_two_level_suit_responses.TwoDiamonds),
        '2H' : (hearts >= 5, new_two_level_suit_responses.TwoHearts),
        '2S' : (spades >= 5, new_two_level_suit_responses.TwoSpades),
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


class JumpShiftResponseToOpen(ResponseToOneLevelSuitedOpen):
    preconditions = JumpShift.preconditions + [
        InvertedPrecondition(LastBidHasAnnotation(positions.RHO, annotations.TakeoutDouble)),
    ]

    # Jumpshifts must be below game and are off in competition so
    # 1S P 3H is the highest available response jumpshift.
    call_names = ['2D', '2H', '2S', '3C', '3D', '3H']
    # FIXME: Shouldn't this be MinHighCardPoints?
    shared_constraints = [points >= 19, MinLength(5)]


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
    annotations = annotations.NegativeDouble


class OneLevelNegativeDouble(NegativeDouble):
    preconditions = LastBidHasLevel(positions.RHO, 1)
    shared_constraints = points >= 6


class TwoLevelNegativeDouble(NegativeDouble):
    preconditions = LastBidHasLevel(positions.RHO, 2)
    shared_constraints = points >= 8


negative_doubles = set([OneLevelNegativeDouble, TwoLevelNegativeDouble])


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
    # FIXME: These should have ordered conditional priorities, no?
    priority = two_clubs_response_priorities.SuitResponse


class NotrumpResponseToStrongTwoClubs(ResponseToStrongTwoClubs):
    call_names = '2N'
    shared_constraints = points >= 8
    priority = two_clubs_response_priorities.NoBiddableSuit


class OpenerRebid(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Opening)


class RebidAfterOneLevelOpen(OpenerRebid):
    # FIXME: Most subclasses here only make sense over a minimum rebid from partner.
    preconditions = LastBidHasAnnotation(positions.Me, annotations.OneLevelSuitOpening),


class NotrumpJumpRebid(RebidAfterOneLevelOpen):
    # See KBB's NotrumpJumpRebid for discussion of cases for this bid.
    # Unclear how this is affected by competition?
    annotations = annotations.NotrumpSystemsOn
    # FIXME: Does this only apply over minors?  What about 1H P 1S P 2N?
    preconditions = JumpFromLastContract(exact_size=1)
    call_names = '2N'
    shared_constraints = [
        points >= 18,
        points <= 19,
        balanced,
    ]


class RebidOneNotrumpByOpener(RebidAfterOneLevelOpen):
    preconditions = InvertedPrecondition(LastBidWas(positions.Partner, 'P'))
    call_names = '1N'
    shared_constraints = NO_CONSTRAINTS


class NotrumpInvitationByOpener(RebidAfterOneLevelOpen):
    preconditions = [NotJumpFromLastContract(), HaveFit()]
    # If we're not balanced, than we'd have a HelpSuitGameTry to use instead.
    call_names = '2N'
    shared_constraints = [points >= 16, balanced]


opener_one_level_new_major = enum.Enum(
    # Up the line with 4s...
    "NewSuitHearts",
    "NewSuitSpades",
)
rule_order.order(*reversed(opener_one_level_new_major))


class NewOneLevelMajorByOpener(RebidAfterOneLevelOpen):
    preconditions = UnbidSuit()
    # FIXME: Should this prefer Hearts over Spades: 1C P 1D P 1H with 4-4 in majors?
    # If partner is expected to prefer 4-card majors over minors then 1H seems impossible?
    priorities_per_call = {
        '1H': opener_one_level_new_major.NewSuitHearts,
        '1S': opener_one_level_new_major.NewSuitSpades,
    }
    shared_constraints = MinLength(4)


class SecondSuitFromOpener(RebidAfterOneLevelOpen):
    preconditions = [
        NotJumpFromLastContract(),
        UnbidSuit(),
        InvertedPrecondition(HaveFit()),
    ]


opener_higher_level_new_suits = enum.Enum(
    "NewSuitHearts", # If you're 4.0.4.5, prefer the major, no?
    "NewSuitClubs", # If you're 4.4.0.5, up the line...
    "NewSuitDiamonds",
)
rule_order.order(*reversed(opener_higher_level_new_suits))


opener_higher_level_new_minors = set([
    opener_higher_level_new_suits.NewSuitClubs,
    opener_higher_level_new_suits.NewSuitDiamonds,
])

opener_higher_level_new_major = opener_higher_level_new_suits.NewSuitHearts


class NewSuitByOpener(SecondSuitFromOpener):
    preconditions = SuitLowerThanMyLastSuit()
    # If you're 4.4.0.5 and the bidding goes 1S P 1H P, do you prefer 2C or 2D?
    constraints = {
        '2C': (NO_CONSTRAINTS, opener_higher_level_new_suits.NewSuitClubs),
        '2D': (NO_CONSTRAINTS, opener_higher_level_new_suits.NewSuitDiamonds),
        '2H': (NO_CONSTRAINTS, opener_higher_level_new_suits.NewSuitHearts),
        # 2S would necessarily be a reverse, or a jump shift, and is not covered by this rule.

        '3C': (MinimumCombinedPoints(25), opener_higher_level_new_suits.NewSuitClubs),
        '3D': (MinimumCombinedPoints(25), opener_higher_level_new_suits.NewSuitDiamonds),
        '3H': (MinimumCombinedPoints(25), opener_higher_level_new_suits.NewSuitHearts),
        # 3S would necessarily be a reverse, or a jump shift, and is not covered by this rule.
    }
    shared_constraints = MinLength(4)


reverse_preconditions = [
    InvertedPrecondition(SuitLowerThanMyLastSuit()),
    LastBidHasSuit(positions.Me),
    UnbidSuit(),
    NotJumpFromLastContract(),
]


opener_reverses = enum.Enum(
    # FIXME: With 5.0.4.4 which do you reverse to?
    "ReverseSpades",
    "ReverseHearts",
    "ReverseDiamonds",
)
rule_order.order(*reversed(opener_reverses))

opener_reverse_to_a_minor = opener_reverses.ReverseDiamonds,

opener_reverse_to_a_major = set([
    opener_reverses.ReverseSpades,
    opener_reverses.ReverseHearts,
])

class ReverseByOpener(SecondSuitFromOpener):
    preconditions = reverse_preconditions
    constraints = {
        # 2C is never a reverse
        '2D': (MinimumCombinedPoints(22), opener_reverses.ReverseDiamonds),
        '2H': (MinimumCombinedPoints(22), opener_reverses.ReverseHearts),
        '2S': (MinimumCombinedPoints(22), opener_reverses.ReverseSpades),

        # 3C is also never a reverse
        '3D': (MinimumCombinedPoints(25), opener_reverses.ReverseDiamonds),
        '3H': (MinimumCombinedPoints(25), opener_reverses.ReverseHearts),
        '3S': (MinimumCombinedPoints(25), opener_reverses.ReverseSpades),
    }
    shared_constraints = MinLength(4)


class SupportPartnerSuit(RebidAfterOneLevelOpen):
    preconditions = [
        InvertedPrecondition(RebidSameSuit()),
        RaiseOfPartnersLastSuit(),
    ]


opener_support_majors = enum.Enum(
    "MajorMax",
    "MajorLimit",
    "MajorMin",
)
rule_order.order(*reversed(opener_support_majors))


class SupportPartnerMajorSuit(SupportPartnerSuit):
    constraints = {
        ('2H', '2S'): (NO_CONSTRAINTS, opener_support_majors.MajorMin),
        ('3H', '3S'): (MinimumCombinedSupportPoints(22), opener_support_majors.MajorLimit),
        ('4H', '4S'): (MinimumCombinedSupportPoints(25), opener_support_majors.MajorMax),
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


class ForcedRebidOriginalSuitByOpener(MinimumRebidOriginalSuitByOpener):
    preconditions = ForcedToBid()
    call_names = ['2C', '2D', '2H', '2S']
    conditional_priorities = [
        (MinLength(6), UnforcedRebidOriginalSuitByOpener),
    ]
    shared_constraints = MinLength(5)


class UnsupportedRebid(RebidOriginalSuitByOpener):
    preconditions = MaxShownLength(positions.Partner, 0)


opener_unsupported_rebids = enum.Enum(
    "GameForcingMinor",
    "InvitationalMajor",
    "InvitationalMinor",
)
rule_order.order(*reversed(opener_unsupported_rebids))

opener_unsupported_minor_rebid = set([
    opener_unsupported_rebids.GameForcingMinor,
    opener_unsupported_rebids.InvitationalMinor,
])


opener_unsupported_major_rebid = opener_unsupported_rebids.InvitationalMajor


class InvitationalUnsupportedRebidByOpener(UnsupportedRebid):
    preconditions = JumpFromLastContract()
    priorities_per_call = {
        ('3C', '3D'): opener_unsupported_rebids.InvitationalMinor,
        ('3H', '3S'): opener_unsupported_rebids.InvitationalMajor,
    }
    shared_constraints = MinLength(6), points >= 16


# Mentioned as "double jump rebid his own suit", p56.
# Only thing close to an example is h19, p56 which has sufficient HCP for a game (even if not fit).
class GameForcingUnsupportedRebidByOpener(UnsupportedRebid):
    preconditions = JumpFromLastContract()
    # I doubt we want to jump to game w/o support from our partner.  He's shown 6 points...
    # Maybe this is for extremely unbalanced hands, like 7+?
    call_names = ['4C', '4D']
    shared_constraints = MinLength(6), points >= 19
    priority = opener_unsupported_rebids.GameForcingMinor


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


opener_jumpshifts = enum.Enum(
    # It's possible to have 0.4.4.5 and we'd rather jump-shift to hearts than diamonds, no?
    "JumpShiftToSpades",
    "JumpShiftToHearts",
    "JumpShiftToDiamonds",
    "JumpShiftToClubs",
)
rule_order.order(*reversed(opener_jumpshifts))


opener_jumpshifts_to_minors = set([
    opener_jumpshifts.JumpShiftToDiamonds,
    opener_jumpshifts.JumpShiftToClubs,
])


opener_jumpshifts_to_majors = set([
    opener_jumpshifts.JumpShiftToSpades,
    opener_jumpshifts.JumpShiftToHearts,
])


class JumpShiftByOpener(RebidAfterOneLevelOpen):
    preconditions = JumpShift.preconditions
    # The lowest possible jumpshift is 1C P 1D P 2H.
    # The highest possible jumpshift is 1S P 2S P 4H
    priorities_per_call = {
        (      '3C', '4C'): opener_jumpshifts.JumpShiftToClubs,
        (      '3D', '4D'): opener_jumpshifts.JumpShiftToDiamonds,
        ('2H', '3H', '4H'): opener_jumpshifts.JumpShiftToHearts,
        ('2S', '3S',     ): opener_jumpshifts.JumpShiftToSpades,
    }
    # FIXME: The book mentions that opener jumpshifts don't always promise 4, especially for 1C P MAJOR P 3D
    shared_constraints = (points >= 19, MinLength(4))


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
    annotations = annotations.NotrumpSystemsOn
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
        # z3 is often smart enough to know that partner has 3 in a suit
        # when re-bidding 1N, but that doesn't mean our (unforced) bid
        # of that new suit would be a sign-off!
        # FIXME: Perhaps this should required ForcedToBid()?
        DidBidSuit(positions.Partner),
    ]
    call_names = ['2C', '2D', '2H', '2S']
    shared_constraints = MinimumCombinedLength(7)


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


class FourthSuitForcingPrecondition(Precondition):
    def fits(self, history, call):
        if annotations.FourthSuitForcing in history.annotations:
            return False
        return len(history.us.bid_suits) == 3 and len(history.them.bid_suits) == 0


class SufficientPointsForFourthSuitForcing(Constraint):
    def expr(self, history, call):
        return points >= max(0, points_for_sound_notrump_bid_at_level[call.level] - history.partner.min_points)

fourth_suit_forcing_priorties = enum.Enum(
    "TwoLevel",
    "ThreeLevel",
)
# No need for ordering because at most one is available at any time.

class FourthSuitForcing(Rule):
    category = categories.Gadget
    preconditions = [
        LastBidHasSuit(positions.Partner),
        FourthSuitForcingPrecondition(),
        UnbidSuit(),
    ]
    annotations = annotations.FourthSuitForcing
    shared_constraints = [
        SufficientPointsForFourthSuitForcing(),
        ConstraintNot(Stopper()),
    ]


class NonJumpFourthSuitForcing(FourthSuitForcing):
    preconditions = NotJumpFromPartnerLastBid()
    # Smallest: 1D,1H,1S,2C
    # Largest: 1H,2D,3C,3S
    call_names = [
        '2C', '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
    ]
    priorities_per_call = {
        ('2C', '2D', '2H', '2S'): fourth_suit_forcing_priorties.TwoLevel,
        ('3C', '3D', '3H', '3S'): fourth_suit_forcing_priorties.ThreeLevel,
    }


class TwoSpadesJumpFourthSuitForcing(FourthSuitForcing):
    preconditions = JumpFromPartnerLastBid(exact_size=1)
    call_names = '2S'
    priority = fourth_suit_forcing_priorties.TwoLevel


fourth_suit_forcing_response_priorities = enum.Enum(
    "JumpToThreeNotrump",
    "Notrump",
    "DelayedSupport",
    # "SecondSuit",
    "FourthSuit",
)
rule_order.order(*reversed(fourth_suit_forcing_response_priorities))

rebid_response_to_fourth_suit_forcing_priorities = enum.Enum(*suited_calls())
rule_order.order(*reversed(rebid_response_to_fourth_suit_forcing_priorities))

rule_order.order(
    rebid_response_to_fourth_suit_forcing_priorities,
    fourth_suit_forcing_response_priorities
)

class ResponseToFourthSuitForcing(Rule):
    category = categories.Gadget
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.FourthSuitForcing)


class StopperInFouthSuit(Constraint):
    def expr(self, history, call):
        strain = history.partner.last_call.strain
        return stopper_expr_for_suit(strain)


class NotrumpResponseToFourthSuitForcing(ResponseToFourthSuitForcing):
    preconditions = NotJumpFromLastContract()
    call_names = ['2N', '3N']
    priority = fourth_suit_forcing_response_priorities.Notrump
    shared_constraints = StopperInFouthSuit()


class NotrumpJumpResponseToFourthSuitForcing(ResponseToFourthSuitForcing):
    preconditions = JumpFromLastContract()
    call_names = '3N'
    priority = fourth_suit_forcing_response_priorities.JumpToThreeNotrump
    shared_constraints = [StopperInFouthSuit(), MinimumCombinedPoints(25)]


class DelayedSupportResponseToFourthSuitForcing(ResponseToFourthSuitForcing):
    preconditions = [
        NotJumpFromLastContract(),
        DidBidSuit(positions.Partner),
    ]
    call_names = [
              '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
        '4C', '4D', '4H',
    ]
    priority = fourth_suit_forcing_response_priorities.DelayedSupport
    shared_constraints = MinimumCombinedLength(7)


class RebidResponseToFourthSuitForcing(ResponseToFourthSuitForcing):
    preconditions = [
        NotJumpFromLastContract(),
        DidBidSuit(positions.Me),
    ]
    # FIXME: The higher call should show additional length in that suit.
    priorities_per_call = {
        '2D': rebid_response_to_fourth_suit_forcing_priorities.get('2D'),
        '2H': rebid_response_to_fourth_suit_forcing_priorities.get('2H'),
        '2S': rebid_response_to_fourth_suit_forcing_priorities.get('2S'),

        '3C': rebid_response_to_fourth_suit_forcing_priorities.get('3C'),
        '3D': rebid_response_to_fourth_suit_forcing_priorities.get('3D'),
        '3H': rebid_response_to_fourth_suit_forcing_priorities.get('3H'),
        '3S': rebid_response_to_fourth_suit_forcing_priorities.get('3S'),

        '4C': rebid_response_to_fourth_suit_forcing_priorities.get('4C'),
        '4D': rebid_response_to_fourth_suit_forcing_priorities.get('4D'),
        '4H': rebid_response_to_fourth_suit_forcing_priorities.get('4H'),
    }
    shared_constraints = NO_CONSTRAINTS


class FourthSuitResponseToFourthSuitForcing(ResponseToFourthSuitForcing):
    preconditions = [
        NotJumpFromLastContract(),
        UnbidSuit(),
    ]
    call_names = [
        '3C', '3D', '3H', '3S',
        '4C', '4D', '4H', '4S',
    ]
    priority = fourth_suit_forcing_response_priorities.FourthSuit
    shared_constraints = [
        MinLength(4),
        SufficientCombinedPoints(),
    ]


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
    shared_constraints = points < 3
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
    "RedoubleTransferToMinor",
    "TwoSpadesRelay",
    "GarbageStayman",
)
rule_order.order(*reversed(nt_response_priorities))


class NotrumpResponse(Rule):
    category = categories.NotrumpSystem
    preconditions = [
        # 1N overcalls have systems on too, partner does not have to have opened
        LastBidHasAnnotation(positions.Partner, annotations.NotrumpSystemsOn),
    ]


class NotrumpGameInvitation(NotrumpResponse):
    # This is an explicit descriptive rule, not a ToPlay rule.
    # ToPlay is 7-9, but 7 points isn't in game range.
    constraints = { '2N': MinimumCombinedPoints(23) }
    priority = nt_response_priorities.NotrumpGameInvitation


class NotrumpGameAccept(NotrumpResponse):
    # This is an explicit descriptive rule, not a ToPlay rule.
    constraints = { '3N': MinimumCombinedPoints(25) }
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
class TwoLevelStayman(NotrumpResponse):
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


class BasicStayman(NotrumpResponse):
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


class NotrumpTransferResponse(NotrumpResponse):
    annotations = annotations.Transfer


class JacobyTransferToHearts(NotrumpTransferResponse):
    preconditions = NotJumpFromPartnerLastBid()
    call_names = ['2D', '3D', '4D']
    shared_constraints = hearts >= 5
    # Two-level transfers have special rules for setting up a game force sequence with 5-5
    conditional_priorities_per_call = {
        '2D': [(z3.And(hearts == spades, points >= 10), nt_response_priorities.JacobyTransferToHeartsWithGameForcingValues)],
    }
    conditional_priorities = [
        (hearts > spades, nt_response_priorities.JacobyTransferToLongerMajor),
    ]
    priority = nt_response_priorities.JacobyTransferToHearts


class JacobyTransferToSpades(NotrumpTransferResponse):
    preconditions = NotJumpFromPartnerLastBid()
    call_names = ['2H', '3H', '4H']
    shared_constraints = spades >= 5
    # Two-level transfers have special rules for setting up a game force sequence with 5-5
    conditional_priorities_per_call = {
        '2H': [(z3.And(hearts == spades, points >= 10), nt_response_priorities.JacobyTransferToSpadesWithGameForcingValues)],
    }
    conditional_priorities = [
        (spades > hearts, nt_response_priorities.JacobyTransferToLongerMajor),
    ]
    priority = nt_response_priorities.JacobyTransferToSpades


class TwoSpadesRelay(NotrumpTransferResponse):
    constraints = {
        '2S': z3.Or(diamonds >= 6, clubs >= 6),
    }
    priority = nt_response_priorities.TwoSpadesRelay


class QuantitativeFourNotrumpJumpConstraint(Constraint):
    def expr(self, history, call):
        # Invites opener to bid 6N if at a maxium, otherwise pass.
        return points + history.partner.max_points >= 33


class QuantitativeFourNotrumpJump(NotrumpResponse):
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


class RebidAfterJacobyTransfer(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Transfer)
    # Our initial transfer could have been with 0 points, rebidding shows points.
    shared_constraints = points >= 8


class SpadesRebidAfterHeartsTransfer(RebidAfterJacobyTransfer):
    preconditions = LastBidWas(positions.Me, '2D')
    # FIXME: We should not need to manually cap 2S.  We can infer that we have < 10 or we would have transfered to hearts first.
    # FIXME: If we had a 6-5 we would raise directly to game instead of bothering to mention the other major?
    constraints = { '2S': z3.And(spades >= 5, points >= 8, points <= 9) }


hearts_rebids_after_spades_transfers = enum.Enum(
    "SlamInterest",
    "NoSlamInterest",
)
rule_order.order(*reversed(hearts_rebids_after_spades_transfers))


class HeartsRebidAfterSpadesTransfer(RebidAfterJacobyTransfer):
    preconditions = LastBidWas(positions.Me, '2H')
    constraints = {
        # A 3H rebid shows slam interest.  Currently assuming that's 13+?
        # Maybe the 3H bid requires_planning?
        '3H': (points >= 13, hearts_rebids_after_spades_transfers.SlamInterest),
        # A jump to 4H and partner choses 4H or 4S, no slam interest. p11
        '4H': (points >= 10, hearts_rebids_after_spades_transfers.NoSlamInterest),
    }
    shared_constraints = hearts >= 5


class NewMinorRebidAfterJacobyTransfer(RebidAfterJacobyTransfer):
    call_names = '3C', '3D'
    # Minors are not worth mentioning after a jacoby transfer unless we have 5 of them and game-going values.
    # FIXME: It seems like this should imply some number of honors in the bid suit, but there may be times
    # when we have 5+ spot cards in a minor and this looks better than bidding 3N.
    shared_constraints = [MinLength(5), MinimumCombinedPoints(25)]


stayman_response_priorities = enum.Enum(
    "HeartStaymanResponse",
    "SpadeStaymanResponse",
    "DiamondStaymanResponse",
    "PassStaymanResponse",
)
rule_order.order(*reversed(stayman_response_priorities))


class StaymanResponse(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Stayman)
    category = categories.NotrumpSystem


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


class ResponseToOneNotrump(NotrumpResponse):
    preconditions = LastBidWas(positions.Partner, '1N')


class LongMinorGameInvitation(ResponseToOneNotrump):
    call_names = ['3C', '3D']
    shared_constraints = [MinLength(6), TwoOfTheTopThree(), points >= 5]
    # FIXME: Should use the longer suit preference pattern.
    priority = nt_response_priorities.LongMinorGameInvitation


class LongMajorSlamInvitation(ResponseToOneNotrump):
    call_names = ['3H', '3S']
    shared_constraints = [MinLength(6), TwoOfTheTopThree(), points >= 14]
    # FIXME: Should use the longer suit preference pattern.
    priority = nt_response_priorities.LongMajorSlamInvitation


class StaymanRebid(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Stayman)
    category = categories.NotrumpSystem


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


class RedoubleTransferToMinor(NotrumpResponse):
    preconditions = [
        LastBidWas(positions.Partner, '1N'),
        LastBidWas(positions.RHO, 'X'),
    ]
    call_names = 'XX'
    annotations = annotations.Transfer
    category = categories.Relay
    shared_constraints = z3.And(
        z3.Or(diamonds >= 6, clubs >= 6),
        points <= 4, # NT is likely to be uncomfortable.
    )
    priority = nt_response_priorities.RedoubleTransferToMinor


# FIXME: Should share code with AcceptTransfer, except NotJumpFromPartner's LastBid is confused by 'XX'
class AcceptTransferToTwoClubs(Rule):
    category = categories.Relay
    call_names = '2C'
    preconditions = [
        LastBidWas(positions.Partner, 'XX'),
        LastBidWas(positions.RHO, 'P'),
        LastBidHasAnnotation(positions.Partner, annotations.Transfer),
    ]
    annotations = annotations.Artificial
    priority = relay_priorities.Accept
    shared_constraints = NO_CONSTRAINTS


class ResponseAfterTransferToTwoClubs(Rule):
    category = categories.Relay
    preconditions = [
        LastBidWas(positions.Partner, '2C'),
        LastBidHasAnnotation(positions.Me, annotations.Transfer),
    ]
    constraints = {
        'P': clubs >= 6,
        '2D': diamonds >= 6,
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
    ]
    shared_constraints = [
        MinLength(5),
        ThreeOfTheTopFiveOrBetter(),
        # With 4 cards in RHO's suit, we're likely to be doubled.
        MaxLengthInLastContractSuit(3),
    ]
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
    # FIXME: This should use support points.
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
    shared_constraints = [points >= 15, points <= 18, balanced, StopperInRHOSuit()]
    priority = overcall_priorities.DirectOvercall1N
    annotations = annotations.NotrumpSystemsOn


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
    shared_constraints = z3.Or(z3.And(6 <= points, points <= 12), 15 <= points)


class DirectMichaelsCuebid(MichaelsCuebid, DirectOvercall):
    pass


class BalancingMichaelsCuebid(MichaelsCuebid, BalancingOvercall):
    pass


class MichaelsMinorRequest(Rule):
    preconditions = [
        LastBidHasAnnotation(positions.Partner, annotations.MichaelsCuebid),
        # The minor is only ambigious if the cuebid was a major.
        LastBidHasStrain(positions.Partner, suit.MAJORS),
        NotJumpFromLastContract(),
    ]
    requires_planning = True
    call_names = ['2N', '4C', '4N']
    annotations = annotations.MichaelsMinorRequest
    shared_constraints = NO_CONSTRAINTS


class ResponseToMichaelsMinorRequest(Rule):
    # FIXME: Should this be on if RHO bid?
    # If RHO bid the other minor is it already obvious which we have?
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.MichaelsMinorRequest)


class SuitResponseToMichaelsMinorRequest(ResponseToMichaelsMinorRequest):
    preconditions = NotJumpFromLastContract()
    call_names = (
        '3C', '3D',
              '4D',
        '5C', '5D',
    )
    shared_constraints = MinLength(5)


class PassResponseToMichaelsMinorRequest(ResponseToMichaelsMinorRequest):
    # The book doesn't cover this, but if 4C was the minor request, lets interpret a pass
    # as meaning "I have clubs" and am weak (game is already remote).
    preconditions = LastBidWas(positions.Partner, '4C')
    call_names = 'P'
    shared_constraints = clubs >= 5


# Pass instead of 5C when we can.
rule_order.order(SuitResponseToMichaelsMinorRequest, PassResponseToMichaelsMinorRequest)


# FIXME: Missing Jump responses to Michael's minor request.
# They're used for showing that we're a big michaels.


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
        InvertedPrecondition(LastBidWas(positions.Me, 'X')),
        # LastBidWasNaturalSuit(),
        # LastBidWasBelowGame(),
        UnbidSuitCountRange(2, 3),
    ]
    annotations = annotations.TakeoutDouble
    shared_constraints = ConstraintOr(SupportForUnbidSuits(), points >= 17)
    priority = overcall_priorities.TakeoutDouble


takeout_double_after_preempt_precondition = AndPrecondition(
    EitherPrecondition(
        LastBidHasAnnotation(positions.RHO, annotations.Preemptive),
        LastBidHasAnnotation(positions.LHO, annotations.Preemptive),
    ),
    InvertedPrecondition(HasBid(positions.Me)),
)


class OneLevelTakeoutDouble(TakeoutDouble):
    preconditions = [
        Level(1),
        InvertedPrecondition(takeout_double_after_preempt_precondition),
    ]
    # FIXME: Why isn't this 12?  NaturalSuited can only respond to 12+ points currently.
    shared_constraints = points >= 11


class TwoLevelTakeoutDouble(TakeoutDouble):
    preconditions = [
        Level(2),
        InvertedPrecondition(takeout_double_after_preempt_precondition),
    ]
    shared_constraints = points >= 15


class TakeoutDoubleAfterPreempt(TakeoutDouble):
    preconditions = takeout_double_after_preempt_precondition
    shared_constraints = points >= 11


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
    preconditions = [SuitUnbidByOpponents(), NotJumpFromLastContract()]
    # FIXME: Why is the min-length constraint necessary?
    shared_constraints = [MinLength(3), LongestSuitExceptOpponentSuits()]
    # Need conditional priorities to disambiguate cases like being 1.4.4.4 with 0 points after 1C X P
    # Similarly after 1H X P, with 4 spades and 4 clubs, but with xxxx spades and AKQx clubs, do we bid clubs or spades?
    priorities_per_call = {
        (      '2C', '3C'): takeout_double_responses.ThreeCardClubResonseToTakeoutDouble,
        ('1D', '2D', '3D'): takeout_double_responses.ThreeCardDiamondResonseToTakeoutDouble,
        ('1H', '2H', '3H'): takeout_double_responses.ThreeCardHeartResonseToTakeoutDouble,
        ('1S', '2S'      ): takeout_double_responses.ThreeCardSpadeResonseToTakeoutDouble,
    }
    conditional_priorities_per_call = {
        (      '2C', '3C'): [(clubs >= 4, takeout_double_responses.ClubResonseToTakeoutDouble)],
        ('1D', '2D', '3D'): [(diamonds >= 4, takeout_double_responses.DiamondResonseToTakeoutDouble)],
        ('1H', '2H', '3H'): [(hearts >= 4, takeout_double_responses.HeartResonseToTakeoutDouble)],
        ('1S', '2S'      ): [(spades >= 4, takeout_double_responses.SpadeResonseToTakeoutDouble)],
    }


class JumpSuitResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = [SuitUnbidByOpponents(), JumpFromLastContract(exact_size=1)]
    # You can have 10 points, but no stopper in opponents suit and only a 3 card suit to bid.
    # 1C X P, xxxx.Axx.Kxx.Kxx
    shared_constraints = [MinLength(3), LongestSuitExceptOpponentSuits(), points >= 10]
    priorities_per_call = {
        (      '3C', '4C'): takeout_double_responses.ThreeCardJumpClubResonseToTakeoutDouble,
        ('2D', '3D', '4D'): takeout_double_responses.ThreeCardJumpDiamondResonseToTakeoutDouble,
        ('2H', '3H', '4H'): takeout_double_responses.ThreeCardJumpHeartResonseToTakeoutDouble,
        ('2S', '3S'      ): takeout_double_responses.ThreeCardJumpSpadeResonseToTakeoutDouble,
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
    call_names = [
        '2C', '2D', '2H', '2S',
        '3C', '3D', '3H', '3S'
    ]
    # FIXME: 4+ in the available majors?
    shared_constraints = [points >= 13, SupportForUnbidSuits()]


# NOTE: I don't think we're going to end up needing most of these.
rebids_after_takeout_double = enum.Enum(
    "CueBidAfterTakeoutDouble",

    "JumpMajorRaise",
    "MajorRaise",

    "ThreeNotrumpAfterTakeoutDouble",

    "JumpSpadesNewSuit",
    "SpadesNewSuit",
    "JumpHeartsNewSuit",
    "HeartsNewSuit",

    "TwoNotrumpAfterTakeoutDouble",
    "OneNotrumpAfterTakeoutDouble",

    "JumpMinorRaise",
    "MinorRaise",

    "JumpDiamondsNewSuit",
    "DiamondsNewSuit",
    "JumpClubsNewSuit",
    "ClubsNewSuit",

    "TakeoutDoubleAfterTakeoutDouble",
)
rule_order.order(*reversed(rebids_after_takeout_double))


class RebidAfterTakeoutDouble(Rule):
    # FIXME: These only apply after a minimum (non-jump?) response from partner.
    preconditions = LastBidHasAnnotation(positions.Me, annotations.TakeoutDouble)
    shared_constraints = points >= 17


class PassAfterTakeoutDouble(Rule):
    preconditions = [
        LastBidHasAnnotation(positions.Me, annotations.TakeoutDouble),
        LastBidWas(positions.LHO, 'P'), # If LHO bid up, we don't necessarily have < 17hcp.
        LastBidWas(positions.RHO, 'P'),
    ]
    call_names = 'P'
    shared_constraints = points < 17


class RaiseAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = [
        LastBidWas(positions.RHO, 'P'),
        RaiseOfPartnersLastSuit(),
        NotJumpFromLastContract()
    ]
    # Min: 1C X 1D P 2D, Max: 2S X P 3H P 4H
    # FIXME: Game doesn't seem like a raise here?
    priorities_per_call = {
        (      '3C', '4C'): rebids_after_takeout_double.MinorRaise,
        ('2D', '3D', '4D'): rebids_after_takeout_double.MinorRaise,
        ('2H', '3H', '4H'): rebids_after_takeout_double.MajorRaise,
        ('2S', '3S'      ): rebids_after_takeout_double.MajorRaise,
    }
    shared_constraints = MinLength(4)


class JumpRaiseAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = [
        RaiseOfPartnersLastSuit(),
        JumpFromPartnerLastBid(exact_size=1)
    ]
    # Min: 1C X 1D P 3D, Max: 2S X P 3D P 5D
    # FIXME: Game doesn't seem like a raise here?
    priorities_per_call = {
        (      '3C', '4C', '5C'): rebids_after_takeout_double.JumpMinorRaise,
        ('2D', '3D', '4D', '5D'): rebids_after_takeout_double.JumpMinorRaise,
        ('2H', '3H', '4H'      ): rebids_after_takeout_double.JumpMajorRaise,
        ('2S', '3S', '4S'      ): rebids_after_takeout_double.JumpMajorRaise,
    }
    shared_constraints = [MinLength(4), points >= 19]


class NewSuitAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = [
        UnbidSuit(),
        NotJumpFromLastContract(),
        # FIXME: Remove !RaiseOfPartnersLastSuit once SuitResponseToTakeoutDouble implies 4+ (even though it
        # only needs 3+ to make the bid).  Promising only 3 is currently confusing UnbidSuit.
        InvertedPrecondition(RaiseOfPartnersLastSuit()),
    ]
    # Min: 1C X XX P 1D, Max: 2D X P 2S 3H
    priorities_per_call = {
        (      '2C', '3C'): rebids_after_takeout_double.ClubsNewSuit,
        ('1D', '2D', '3D'): rebids_after_takeout_double.DiamondsNewSuit,
        ('1H', '2H', '3H'): rebids_after_takeout_double.HeartsNewSuit,
        ('1S', '2S'      ): rebids_after_takeout_double.SpadesNewSuit,
    }
    shared_constraints = MinLength(5)


class JumpNewSuitAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = [
        UnbidSuit(),
        JumpFromLastContract(exact_size=1),
        # FIXME: Remove !RaiseOfPartnersLastSuit once SuitResponseToTakeoutDouble implies 4+ (even though it
        # only needs 3+ to make the bid).  Promising only 3 is currently confusing UnbidSuit.
        InvertedPrecondition(RaiseOfPartnersLastSuit()),
    ]
    # Min: 1C X XX P 2D, Max: 2S X P 3C 5D
    # FIXME: Jumping straight to game seems less useful than a cuebid would?
    priorities_per_call = {
        (      '3C', '4C', '5C'): rebids_after_takeout_double.JumpClubsNewSuit,
        ('2D', '3D', '4D', '5D'): rebids_after_takeout_double.JumpDiamondsNewSuit,
        ('2H', '3H', '4H'      ): rebids_after_takeout_double.JumpHeartsNewSuit,
        ('2S', '3S', '4S'      ): rebids_after_takeout_double.JumpSpadesNewSuit,

    }
    shared_constraints = [MinLength(6), TwoOfTheTopThree(), points >= 21]


class NotrumpAfterTakeoutDouble(RebidAfterTakeoutDouble):
    constraints = {
        '1N': (points >= 18, rebids_after_takeout_double.OneNotrumpAfterTakeoutDouble),
        # 2N depends on whether it is a jump.
        '3N': (points >= 23, rebids_after_takeout_double.ThreeNotrumpAfterTakeoutDouble), # FIXME: Techincally means 9+ tricks.
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


class TakeoutDoubleAfterTakeoutDouble(RebidAfterTakeoutDouble):
    call_names = 'X'
    preconditions = [
        LastBidWas(positions.Partner, 'P'),
        MaxLevel(2),
        LastBidHasSuit(),
    ]
    # Doubling a second time shows both 17+ and shortness in the last bid contract.
    # We're asking partner to pick a suit, any suit but don't let them have it.
    shared_constraints = [points >= 17, MaxLengthInLastContractSuit(1)]
    priority = rebids_after_takeout_double.TakeoutDoubleAfterTakeoutDouble


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
    # FIXME: These need some sort of priority ordering between the calls.
    call_names = [
              '2D', '2H', '2S',
        '3C', '3D', '3H', '3S',
        '4C', '4D',
    ]
    shared_constraints = [MinLength(5), MinCombinedPointsForPartnerMinimumSuitedRebid()]


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
    call_names = ['3C', '3D', '3H', '3S']
    # Note: We could have a protected outside honor with as few as 6 points,
    # (QJTxxx in our main suit + Qxx in our outside honor suit)
    # Unittests would suggest we should require 9+?
    shared_constraints = [points >= 9, ThirdRoundStopper()]


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

    rule_order.order(preempt_priorities, opening_priorities)
    rule_order.order(natural_bids, preempt_priorities)
    rule_order.order(natural_bids, overcall_priorities)
    rule_order.order(natural_games, nt_response_priorities, natural_slams)
    rule_order.order(natural_bids, stayman_response_priorities)
    rule_order.order(natural_bids, GarbagePassStaymanRebid)
    rule_order.order(natural_bids, PassAfterTakeoutDouble)
    rule_order.order(natural_bids, two_clubs_opener_rebid_priorities)
    rule_order.order(natural_bids, responder_rebid_priorities)
    rule_order.order(natural_exact_notrump_game, stayman_rebid_priorities.GameForcingOtherMajor, natural_exact_major_games)
    rule_order.order(natural_nt_part_scores, stayman_rebid_priorities.InvitationalOtherMajor, natural_suited_part_scores)
    rule_order.order(takeout_double_responses, natural_bids)
    rule_order.order(ForcedRebidOriginalSuitByOpener, natural_bids)
    rule_order.order(natural_bids, NewSuitResponseToStandardOvercall, CuebidResponseToStandardOvercall)
    rule_order.order(RaiseResponseToStandardOvercall, natural_bids, NewSuitResponseToStandardOvercall, CuebidResponseToStandardOvercall)
    rule_order.order(DefaultPass, RaiseResponseToStandardOvercall)
    rule_order.order(ResponderSignoffInPartnersSuit, natural_bids)
    rule_order.order(DefaultPass, ResponderSignoffInPartnersSuit)
    rule_order.order(DefaultPass, opening_priorities)
    rule_order.order(rebids_after_takeout_double, natural_bids)
    rule_order.order(natural_bids, SecondNegative)
    rule_order.order(DefaultPass, rebids_after_takeout_double)
    rule_order.order(DefaultPass, natural_passses)
    rule_order.order(natural_suited_part_scores, natural_passses)
    rule_order.order(SuitGameIsRemote, natural_games, SuitSlamIsRemote, natural_slams)
    rule_order.order(
        RebidOneNotrumpByOpener,
        opener_one_level_new_major,
        opener_support_majors,
    )
    rule_order.order(
        RebidOneNotrumpByOpener,
        opener_higher_level_new_suits,
    )
    rule_order.order(
        RebidOneNotrumpByOpener,
        opener_reverses,
    )
    rule_order.order(
        ForcedRebidOriginalSuitByOpener,
        opener_higher_level_new_suits,
        opener_one_level_new_major,
    )
    rule_order.order(
        DefaultPass,
        opener_higher_level_new_minors,
        opener_jumpshifts_to_minors,
    )
    rule_order.order(
        opener_higher_level_new_major,
        opener_reverse_to_a_major,
        opener_jumpshifts_to_majors,
    )
    rule_order.order(
        opener_reverse_to_a_minor,
        opener_one_level_new_major,
        opener_jumpshifts_to_majors,
    )
    rule_order.order(
        NotrumpJumpRebid,
        opener_support_majors,
    )
    rule_order.order(
        # Don't jump to game immediately, even if we have the points for it.
        natural_exact_notrump_game,
        opener_one_level_new_major,
    )
    rule_order.order(
        ThreeNotrumpMajorResponse,
        new_one_level_major_responses,
    )
    rule_order.order(
        natural_exact_notrump_game,
        [fourth_suit_forcing_priorties.TwoLevel, fourth_suit_forcing_priorties.ThreeLevel],
    )
    rule_order.order(
        natural_nt_part_scores,
        fourth_suit_forcing_priorties.TwoLevel,
    )
    rule_order.order(
        # FIXME: This seems backwards.
        natural_suited_part_scores,
        fourth_suit_forcing_priorties.TwoLevel,
    )
    rule_order.order(
        [fourth_suit_forcing_priorties.TwoLevel, fourth_suit_forcing_priorties.ThreeLevel],
        responder_rebid_priorities.ThreeLevelSuitRebidByResponder,
    )
    rule_order.order(
        DefaultPass,
        # Mention a 4-card major before rebidding a 6-card minor.
        UnforcedRebidOriginalSuitByOpener,
        opener_one_level_new_major,
    )
    rule_order.order(
        ForcedRebidOriginalSuitByOpener,
        opener_higher_level_new_suits,
    )
    rule_order.order(
        ForcedRebidOriginalSuitByOpener,
        RebidOneNotrumpByOpener,
        UnforcedRebidOriginalSuitByOpener,
    )
    rule_order.order(
        # Rebids will only ever consider one suit, so we won't be comparing majors/minors here.
        ForcedRebidOriginalSuitByOpener,
        UnforcedRebidOriginalSuitByOpener,
        opener_unsupported_rebids,
    )
    rule_order.order(
        natural_suited_part_scores,
        NotrumpInvitationByOpener,
        HelpSuitGameTry,
    )
    rule_order.order(
        # If we have a new suit to mention, we'd rather do that than sign off in game?
        # Maybe game with stoppers should be higher priority and game without lower?
        # 1S P 2C P 2H seems higher priority than a straight jump to game...
        # but 1S P 2C P 2D doesn't seem very useful if we have everything stopped?
        natural_exact_notrump_game,
        opener_higher_level_new_suits,
    )
    rule_order.order(
        opener_higher_level_new_suits,
        opener_support_majors,
    )
    rule_order.order(
        # Definitely rather jump to NT rather than mention a new minor.  Unclear about 2H vs. NT.
        opener_higher_level_new_minors,
        NotrumpJumpRebid,
    )
    rule_order.order(
        ResponderSignoffInPartnersSuit,
        responder_rebid_priorities.ResponderReverse,
    )
    rule_order.order(
        # If we see that game is remote, just stop.
        UnforcedRebidOriginalSuitByOpener,
        natural_passses,
    )
    rule_order.order(
        # FIXME: This may be unecessary once we have responses to negative doubles.
        # But we'd rather place the contract in a suited part score than in NT.
        RebidOneNotrumpByOpener,
        natural_suited_part_scores,
    )
    rule_order.order(
        # We'd rather disclose a 6-card major suit than just jump to NT.
        # FIXME: It's possible this is only an issue due to NaturalNotrump missing stoppers!
        natural_exact_notrump_game,
        opener_unsupported_major_rebid,
    )
    rule_order.order(
        # Showing a second minor seems more useful than showing a longer one.
        opener_unsupported_minor_rebid,
        opener_reverse_to_a_minor,
    )
    rule_order.order(
        OneNotrumpResponse,
        raise_responses,
    )
    rule_order.order(
        DefaultPass,
        raise_responses,
    )
    rule_order.order(
        # We don't need to put this above all raise responses, but it shouldn't hurt.
        raise_responses,
        MajorJumpToGame,
    )
    rule_order.order(
        DefaultPass,
        OneNotrumpResponse, # Any time we can respond we should.
        new_two_level_minor_responses, # But we prefer suits to NT.
        major_raise_responses, # But we'd much rather support our partner's major!
    )
    rule_order.order(
        OneNotrumpResponse,
        new_two_level_major_responses,
    )
    rule_order.order(
        # Relays are extremely high priority, this is likely redundant with other orderings.
        DefaultPass,
        relay_priorities
    )
    rule_order.order(
        NotrumpResponseToMinorOpen,
        new_one_level_major_responses,
    )
    rule_order.order(
        new_two_level_minor_responses,
        new_one_level_major_responses,
    )
    rule_order.order(
        natural_bids,
        two_clubs_response_priorities,
    )
    rule_order.order(
        natural_bids,
        feature_response_priorities,
    )
    rule_order.order(
        # We want to start constructive, not just jump to slam.
        natural_slams,
        # FIXME: This should be a group of game-forcing responses, no?
        JumpShiftResponseToOpen,
    )
    rule_order.order(
        OneNotrumpResponse,
        OneLevelNegativeDouble,
    )
    rule_order.order(
        raise_responses,
        JumpShiftResponseToOpen,
    )
    rule_order.order(
        # We'd rather mention a new major than raise partner's minor
        minor_raise_responses,
        new_one_level_major_responses,
        # But we'd rather raise a major than mention a new one.
        major_raise_responses
    )
    rule_order.order(
        # NegativeDouble is more descriptive than any one-level new suit (when it fits).
        new_one_level_suit_responses,
        OneLevelNegativeDouble,
    )
    rule_order.order(
        OneNotrumpResponse,
        OneLevelNegativeDouble,
    )
    # Constructive responses are always better than placement responses.
    rule_order.order(
        natural_bids,
        new_one_level_suit_responses,
    )
    rule_order.order(
        DefaultPass,
        TwoLevelNegativeDouble,
    )
    rule_order.order(
        major_raise_responses,
        Jacoby2N,
    )
    rule_order.order(
        natural_bids,
        jacoby_2n_response_priorities,
    )
    rule_order.order(
        new_one_level_suit_responses,
        defenses_against_takeout_double,
    )
    rule_order.order(
        minimum_raise_responses,
        defenses_against_takeout_double,
        MajorJumpToGame,
    )
    rule_order.order(
        OneNotrumpResponse,
        NotrumpResponseToMinorOpen,
        defenses_against_takeout_double,
    )
    # The rebid-after-transfer bids are more descriptive than jumping to NT game.
    rule_order.order(
        natural_exact_notrump_game,
        hearts_rebids_after_spades_transfers
    )
    rule_order.order(
        natural_suited_part_scores,
        SpadesRebidAfterHeartsTransfer
    )
    rule_order.order(
        natural_exact_notrump_game,
        NewMinorRebidAfterJacobyTransfer
    )
    rule_order.order(
        # Even a jumpshift to a major seems less descriptive than a 2N rebid.
        opener_jumpshifts,
        NotrumpJumpRebid,
    )
    rule_order.order(
        # Better to raise partner's major than show minors.
        negative_doubles,
        major_raise_responses,
    )
    rule_order.order(
        # Better to show points for NT game than mention a new minor?
        new_two_level_minor_responses,
        ThreeNotrumpMajorResponse,
    )
    rule_order.order(
        natural_nt_part_scores,
        negative_doubles,
    )
    rule_order.order(
        # If we can rebid, that's always better than escaping to a NT partscore.
        # FIXME: This should be escape_to_nt_partscore instead of natural_nt.
        # This ordering is probably overbroad as written!
        natural_nt_part_scores,
        UnforcedRebidOriginalSuitByOpener,
    )
    rule_order.order(
        opener_unsupported_major_rebid,
        opener_jumpshifts,
    )
