# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

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


class DefaultPass(Rule):
    preconditions = [InvertedPrecondition(ForcedToBid())]
    call_names = 'P'
    shared_constraints = NO_CONSTRAINTS
    category = categories.DefaultPass


class NaturalPass(Rule):
    preconditions = [LastBidWas(positions.RHO, 'P')]
    call_names = 'P'
    category = categories.NaturalPass


class NaturalPassWithFit(NaturalPass):
    preconditions = [LastBidHasSuit(positions.Partner)]
    shared_constraints = [MinimumCombinedLength(7, use_last_call_suit=True)]


class SuitGameIsRemote(NaturalPassWithFit):
    preconditions = [LastBidWasBelowGame()]
    shared_constraints = [MaximumCombinedPoints(24)]


class SuitSlamIsRemote(NaturalPassWithFit):
    preconditions = [
        LastBidWasGameOrAbove(),
        LastBidWasBelowSlam(),
    ]
    shared_constraints = [MaximumCombinedPoints(32)]


natural_passses = set([
    SuitGameIsRemote,
    SuitSlamIsRemote,
])
