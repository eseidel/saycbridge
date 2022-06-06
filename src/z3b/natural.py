# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core import suit
from z3b import enum
from z3b.constraints import *
from z3b.model import *
from z3b.preconditions import *
from z3b.rule_compiler import Rule, rule_order, categories
from core.call import Call


def copy_dict(d, keys):
    return {key: d.get(key) for key in keys}


natural = enum.Enum(*Call.suited_names())
notrump_without_stoppers = enum.Enum(*Call.notrump_names())
notrump_with_stoppers = enum.Enum(*Call.notrump_names())


natural_slams = rule_order.order(
    notrump_without_stoppers.get('6N'),

    natural.get('6C'),
    natural.get('6D'),
    natural.get('6H'),
    natural.get('6S'),

    notrump_with_stoppers.get('6N'),
    notrump_without_stoppers.get('7N'),

    natural.get('7C'),
    natural.get('7D'),
    natural.get('7H'),
    natural.get('7S'),

    notrump_with_stoppers.get('7N'),
)


natural_exact_games = rule_order.order(
    notrump_without_stoppers.get('3N'),

    natural.get('5C'),
    natural.get('5D'),

    notrump_with_stoppers.get('3N'),

    natural.get('4H'),
    natural.get('4S'),
)


natural_overly_sufficient_games = rule_order.order(
    notrump_without_stoppers.get('5N'),
    notrump_without_stoppers.get('4N'),

    natural.get('5H'),
    natural.get('5S'),

    notrump_with_stoppers.get('5N'),
    notrump_with_stoppers.get('4N'),
)


natural_part_scores = rule_order.order(
    notrump_without_stoppers.get('2N'),
    notrump_without_stoppers.get('1N'),

    # FIXME: These should have higher priorities than the suited part scores.
    notrump_with_stoppers.get('2N'),
    notrump_with_stoppers.get('1N'),

    natural.get('4C'), natural.get('4D'),
    natural.get('3C'), natural.get('3D'), natural.get('3H'), natural.get('3S'),
    natural.get('2C'), natural.get('2D'), natural.get('2H'), natural.get('2S'),
)


rule_order.order(
    natural_part_scores,
    natural_overly_sufficient_games,
    natural_exact_games,
    natural_slams,
)


natural_bids = set(natural) | set(
    notrump_with_stoppers) | set(notrump_without_stoppers)

natural_exact_minor_games = set([
    natural.get('5C'),
    natural.get('5D'),
])

natural_exact_major_games = set([
    natural.get('4H'),
    natural.get('4S'),
])

natural_exact_notrump_game = set([
    notrump_with_stoppers.get('3N'),
    notrump_without_stoppers.get('3N'),
])

natural_games = set([
    notrump_with_stoppers.get('3N'), notrump_without_stoppers.get('3N'),
    natural.get('4H'), natural.get('4S'), notrump_with_stoppers.get(
        '4N'), notrump_without_stoppers.get('4N'),
    natural.get('5C'), natural.get('5D'), natural.get('5H'), natural.get(
        '5S'), notrump_with_stoppers.get('5N'), notrump_without_stoppers.get('5N'),
])

natural_minor_part_scores = set([
    natural.get('2C'), natural.get('2D'),
    natural.get('3C'), natural.get('3D'),
    natural.get('4C'), natural.get('4D'),
])

natural_major_part_scores = set([
    natural.get('2H'), natural.get('2S'),
    natural.get('3H'), natural.get('3S'),
])

natural_suited_part_scores = natural_minor_part_scores | natural_major_part_scores

natural_nt_part_scores = set([
    notrump_with_stoppers.get('1N'), notrump_without_stoppers.get('1N'),
    notrump_with_stoppers.get('2N'), notrump_without_stoppers.get('2N'),
])


points_for_sound_suited_bid_at_level = [
    #  0   1   2   3   4   5   6   7
    None, 16, 19, 22, 25, 28, 33, 37,
]


points_for_sound_notrump_bid_at_level = [
    #  0   1   2   3   4   5   6   7
    None, 19, 22, 25, 28, 30, 33, 37,
]


class WeHaveShownMorePointsThanThem(Precondition):
    def fits(self, history, call):
        return history.us.min_points > history.them.min_points


class SufficientCombinedPoints(Constraint):
    def expr(self, history, call):
        strain = call.strain
        min_points = None
        if strain == suit.NOTRUMP:
            min_points = points_for_sound_notrump_bid_at_level[call.level]
        else:
            assert strain in suit.SUITS, "%s not in %s" % (strain, suit.SUITS)
            min_points = points_for_sound_suited_bid_at_level[call.level]
        return points >= max(0, min_points - history.partner.min_points)


class SufficientCombinedLength(MinimumCombinedLength):
    def __init__(self):
        MinimumCombinedLength.__init__(self, 8)

    def expr(self, history, call):
        strain = call.strain
        if strain == suit.NOTRUMP:
            return NO_CONSTRAINTS
        return MinimumCombinedLength.expr(self, history, call)


class LengthSatisfiesLawOfTotalTricks(Constraint):
    def expr(self, history, call):
        # Written forward: level = partner_min + my_min - 6
        my_count = call.level + 6 - history.partner.min_length(call.strain)
        return expr_for_suit(call.strain) >= my_count


class Natural(Rule):
    category = categories.Natural


class SoundNaturalBid(Natural):
    shared_constraints = [
        SufficientCombinedLength(), SufficientCombinedPoints()]


class NaturalSuited(SoundNaturalBid):
    preconditions = [
        InvertedPrecondition(LastBidHasAnnotation(
            positions.Partner, annotations.Preemptive)),
        WeHaveShownMorePointsThanThem(),
        PartnerHasAtLeastLengthInSuit(1),
    ]
    priorities_per_call = copy_dict(
        natural, Call.suited_names_between('2C', '7S'))


class LawOfTotalTricks(Rule):
    preconditions = [
        # FIXME: This should only apply over weak bids (only when NaturalSuited does not)?
        PartnerHasAtLeastLengthInSuit(1),
    ]
    priorities_per_call = copy_dict(
        natural, Call.suited_names_between('2C', '5D'))
    shared_constraints = LengthSatisfiesLawOfTotalTricks()
    category = categories.LawOfTotalTricks


class SufficientStoppers(Constraint):
    def _is_jump(self, last_contract, call):
        if not last_contract:
            return call.level > 1
        assert call.strain == suit.NOTRUMP
        if last_contract.strain == suit.NOTRUMP:
            return call.level > last_contract.level + 1
        return call.level > last_contract.level

    def expr(self, history, call):
        if self._is_jump(history.last_contract, call) and not history.partner.is_balanced:
            return StoppersInOpponentsSuits().expr(history, call)
        return NO_CONSTRAINTS


class NaturalNotrump(SoundNaturalBid):
    preconditions = WeHaveShownMorePointsThanThem()
    # The copy_dict is redundant, this is all notrump bids.
    priorities_per_call = copy_dict(
        notrump_without_stoppers, Call.notrump_names_between('1N', '7N'))
    shared_constraints = SufficientStoppers()
    conditional_priorities_per_call = {
        '1N': [(StoppersInOpponentsSuits(), notrump_with_stoppers.get('1N'))],
        '2N': [(StoppersInOpponentsSuits(), notrump_with_stoppers.get('2N'))],
        '3N': [(StoppersInOpponentsSuits(), notrump_with_stoppers.get('3N'))],
        '4N': [(StoppersInOpponentsSuits(), notrump_with_stoppers.get('4N'))],
        '5N': [(StoppersInOpponentsSuits(), notrump_with_stoppers.get('5N'))],
        '6N': [(StoppersInOpponentsSuits(), notrump_with_stoppers.get('6N'))],
        '7N': [(StoppersInOpponentsSuits(), notrump_with_stoppers.get('7N'))],
    }


class DefaultPass(Rule):
    preconditions = InvertedPrecondition(ForcedToBid())
    call_names = 'P'
    shared_constraints = NO_CONSTRAINTS
    category = categories.DefaultPass


class NaturalPass(Rule):
    preconditions = [
        LastBidWas(positions.RHO, 'P'),
        # Natural passes do not apply when preempting.
        WeHaveShownMorePointsThanThem(),
        InvertedPrecondition(ForcedToBid()),
    ]
    call_names = 'P'
    category = categories.NaturalPass


class NaturalPassWithFit(NaturalPass):
    preconditions = [
        LastBidHasSuit(positions.Partner),
        InvertedPrecondition(LastBidHasAnnotation(
            positions.Partner, annotations.Artificial)),
        HaveFit(),
    ]
    shared_constraints = MinimumCombinedLength(7, use_partners_last_suit=True)


class SuitGameIsRemote(NaturalPassWithFit):
    preconditions = LastBidWasBelowGame()
    # FIXME: Shouldn't this be support points?
    shared_constraints = MaximumCombinedPoints(24)


class SuitSlamIsRemote(NaturalPassWithFit):
    preconditions = [
        LastBidWasGameOrAbove(),
        LastBidWasBelowSlam(),
        InvertedPrecondition(LastBidHasStrain(positions.Partner, suit.NOTRUMP))
    ]
    shared_constraints = MaximumCombinedPoints(32)


class NotrumpSlamIsRemote(NaturalPass):
    preconditions = [
        LastBidHasStrain(positions.Partner, suit.NOTRUMP),
        LastBidWasGameOrAbove(),
        LastBidWasBelowSlam(),
    ]
    shared_constraints = MaximumCombinedPoints(32)


game_is_remote_passes = set([
    # FIXME: Need NotrumpGameIsRemote?
    SuitGameIsRemote,
])

slam_is_remote_passes = set([
    SuitSlamIsRemote,
    NotrumpSlamIsRemote,
])

natural_passses = game_is_remote_passes | slam_is_remote_passes


rule_order.order(DefaultPass, natural_passses)
# Suited games are much easier to make, we should prefer those when available.
rule_order.order(NotrumpSlamIsRemote, natural_exact_major_games)
rule_order.order(natural_suited_part_scores, natural_passses)
rule_order.order(
    SuitGameIsRemote,
    natural_exact_games,
)
rule_order.order(
    natural_overly_sufficient_games,
    slam_is_remote_passes,
    natural_slams,
)
