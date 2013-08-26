# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core import suit
from z3b import enum
from z3b.constraints import *
from z3b.model import *
from z3b.preconditions import *
from z3b.rule_compiler import Rule, rule_order, categories


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


points_for_sound_suited_bid_at_level = [
    #  0   1   2   3   4   5   6   7
    None, 16, 19, 22, 25, 28, 33, 37,
]


points_for_sound_notrump_bid_at_level = [
    #  0   1   2   3   4   5   6   7
    None, 19, 22, 25, 28, 30, 33, 37,
]


class SufficientCombinedPoints(Constraint):
    def expr(self, history, call):
        strain = call.strain
        min_points = None
        if strain == suit.NOTRUMP:
            min_points = points_for_sound_notrump_bid_at_level[call.level]
        if strain in suit.SUITS:
            min_points = points_for_sound_suited_bid_at_level[call.level]
        assert min_points is not None
        return points >= max(0, min_points - history.partner.min_points)


class Natural(Rule):
    category = categories.Natural


class SuitedToPlay(Natural):
    preconditions = [
        MinimumCombinedPointsPrecondition(12),
        PartnerHasAtLeastLengthInSuit(1)
    ]
    priorities_per_call = {
        ('2C', '2D'): natural_priorities.TwoLevelNaturalMinor,
        ('2H', '2S'): natural_priorities.TwoLevelNaturalMajor,

        ('3C', '3D'): natural_priorities.ThreeLevelNaturalMinor,
        ('3H', '3S'): natural_priorities.ThreeLevelNaturalMajor,

        ('4C', '4D'): natural_priorities.FourLevelNaturalMinor,
        ('4H', '4S'): natural_priorities.FourLevelNaturalMajor,

        ('5C', '5D'): natural_priorities.FiveLevelNaturalMinor,
        ('5H', '5S'): natural_priorities.FiveLevelNaturalMajor,

        ('6C', '6D'): natural_priorities.SixLevelNaturalMinor,
        ('6H', '6S'): natural_priorities.SixLevelNaturalMajor,

        ('7C', '7D'): natural_priorities.SevenLevelNaturalMinor,
        ('7H', '7S'): natural_priorities.SevenLevelNaturalMajor,
    }
    shared_constraints = [MinimumCombinedLength(8), SufficientCombinedPoints()]


class NotrumpToPlay(Natural):
    priorities_per_call = {
        '1N': natural_priorities.OneLevelNaturalNT,
        '2N': natural_priorities.TwoLevelNaturalNT,
        '3N': natural_priorities.ThreeLevelNaturalNT,
        '4N': natural_priorities.FourLevelNaturalNT,
        '5N': natural_priorities.FiveLevelNaturalNT,
        '6N': natural_priorities.SixLevelNaturalNT,
        '7N': natural_priorities.SevenLevelNaturalNT,
    }
    shared_constraints = [SufficientCombinedPoints()]


class DefaultPass(Rule):
    preconditions = InvertedPrecondition(ForcedToBid())
    call_names = 'P'
    shared_constraints = NO_CONSTRAINTS
    category = categories.DefaultPass


class NaturalPass(Rule):
    preconditions = LastBidWas(positions.RHO, 'P')
    call_names = 'P'
    category = categories.NaturalPass


class NaturalPassWithFit(NaturalPass):
    preconditions = LastBidHasSuit(positions.Partner)
    shared_constraints = MinimumCombinedLength(7, use_last_call_suit=True)


class SuitGameIsRemote(NaturalPassWithFit):
    preconditions = LastBidWasBelowGame()
    shared_constraints = MaximumCombinedPoints(24)


class SuitSlamIsRemote(NaturalPassWithFit):
    preconditions = [
        LastBidWasGameOrAbove(),
        LastBidWasBelowSlam(),
    ]
    shared_constraints = MaximumCombinedPoints(32)


natural_passses = set([
    SuitGameIsRemote,
    SuitSlamIsRemote,
])
