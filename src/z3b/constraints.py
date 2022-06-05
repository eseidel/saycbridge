# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from builtins import object
from z3b.model import expr_for_suit
import z3b.model as model
import z3
from core import suit
from z3b.preconditions import annotations


class Constraint(object):
    def expr(self, history, call):
        raise NotImplementedError


class ConstraintAnd(Constraint):
    def __init__(self, *constraints):
        self.constraints = constraints

    def expr(self, history, call):
        return z3.And([constraint.expr(history, call) if isinstance(constraint, Constraint) else constraint for constraint in self.constraints])


class ConstraintOr(Constraint):
    def __init__(self, *constraints):
        self.constraints = constraints

    def expr(self, history, call):
        return z3.Or([constraint.expr(history, call) if isinstance(constraint, Constraint) else constraint for constraint in self.constraints])


class ConstraintNot(Constraint):
    def __init__(self, constraint):
        self.constraint = constraint

    def expr(self, history, call):
        return z3.Not(self.constraint.expr(history, call))


class MinimumCombinedLength(Constraint):
    def __init__(self, min_count, use_partners_last_suit=False):
        self.min_count = min_count
        self.use_partners_last_suit = use_partners_last_suit

    def expr(self, history, call):
        suit = call.strain
        if self.use_partners_last_suit:
            # We should assert here, except this is used to pass after a transfer accept (which is artificial)
            # assert annotations.Artificial not in history.partner.annotations_for_last_call
            suit = history.partner.last_call.strain
        partner_promised_length = history.partner.min_length(suit)
        implied_length = max(self.min_count - partner_promised_length, 0)
        return expr_for_suit(suit) >= implied_length


class MinimumCombinedPoints(Constraint):
    def __init__(self, min_points):
        self.min_points = min_points

    def expr(self, history, call):
        return model.points >= max(0, self.min_points - history.partner.min_points)


class MinimumCombinedSupportPoints(Constraint):
    def __init__(self, min_points, use_partners_last_suit=False):
        self.min_points = min_points
        self.use_partners_last_suit = use_partners_last_suit

    def expr(self, history, call):
        implied_min_points = max(
            0, self.min_points - history.partner.min_points)
        suit = call.strain
        if self.use_partners_last_suit:
            assert annotations.Artificial not in history.partner.annotations_for_last_call
            suit = history.partner.last_call.strain
        return z3.And(model.support_points_expr_for_suit(suit) >= implied_min_points,
                      model.playing_points >= implied_min_points)


class MinimumSupportPointsForPartnersLastSuit(Constraint):
    def __init__(self, min_points):
        self.min_points = min_points

    def expr(self, history, call):
        # We should assert here, except this is used to pass after a transfer accept (which is artificial)
        # assert annotations.Artificial not in history.partner.annotations_for_last_call
        return model.support_points_expr_for_suit(history.partner.last_call.strain) >= self.min_points


class MaximumSupportPointsForPartnersLastSuit(Constraint):
    def __init__(self, max_points):
        self.max_points = max_points

    def expr(self, history, call):
        assert annotations.Artificial not in history.partner.annotations_for_last_call
        return model.support_points_expr_for_suit(history.partner.last_call.strain) <= self.max_points


class MaximumCombinedPoints(Constraint):
    def __init__(self, max_points):
        self.max_points = max_points

    def expr(self, history, call):
        return model.points <= max(0, self.max_points - history.partner.max_points)


class MinLength(Constraint):
    def __init__(self, min_length, suits=None):
        self.min_length = min_length
        self.suits = suits

    def expr(self, history, call):
        suits = self.suits or [call.strain]
        return z3.And([expr_for_suit(suit) >= self.min_length for suit in suits])


class MaxLength(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def expr(self, history, call):
        return expr_for_suit(call.strain) <= self.max_length


class MaxLengthInLastContractSuit(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def expr(self, history, call):
        return expr_for_suit(history.last_contract.strain) <= self.max_length


class MaxLengthInUnbidMajors(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def expr(self, history, call):
        return z3.And([expr_for_suit(major) <= self.max_length for major in suit.MAJORS if major != call.strain])


# class AdditionalLength(Constraint):
#     def __init__(self, additional_length):
#         self.additional_length = additional_length

#     def expr(self, history, call):
#         strain = history.last_contract.strain
#         return expr_for_suit(strain) >= history.me.min_length(strain) + self.additional_length


class SupportForPartnerLastBid(Constraint):
    def __init__(self, min_count):
        self._min_count = min_count

    def expr(self, history, call):
        partner_suit = history.partner.last_call.strain
        return expr_for_suit(partner_suit) >= self._min_count


class SupportForMultipleSuits(Constraint):
    def _four_in_almost_every_suit(self, missing_suit, suits):
        return z3.And([expr_for_suit(suit) >= 4 for suit in set(suits) - set([missing_suit])])

    def _support_for_suits(self, suits, history):
        if len(suits) == 3:
            three_card_support_expr = z3.And(
                [expr_for_suit(suit) >= 3 for suit in suits])
            four_card_support_expr = z3.Or([self._four_in_almost_every_suit(
                missing_suit, suits) for missing_suit in suits])
            return z3.And(three_card_support_expr, four_card_support_expr)
        if len(suits) == 2:
            return z3.And([expr_for_suit(suit) >= 4 for suit in suits])
        assert False, "%s only supports 2 or 3 unbid suits, found %d: %s" % (
            self.__class__, len(suits), history.call_history)


class SupportForUnbidSuits(SupportForMultipleSuits):
    def expr(self, history, call):
        unbid_suits = history.unbid_suits
        return self._support_for_suits(history.unbid_suits, history)


# We support any suit partner has shown life in.  Used for cuebid responses to doubles.
class SupportForPartnersSuits(SupportForMultipleSuits):
    def expr(self, history, call):
        # This is kinda a hack.  Because TakeoutDouble can be either 17+ hcp or shape
        # we don't know that partner has necessarily bid a suit yet, so we can't just:
        # partners_suits = filter(lambda strain: history.partner.min_length(strain) > 1, suit.SUITS)
        # Instead we take the inverse of suits which ops have bid, which should be the same:
        partners_suits = set(suit.SUITS) - set(history.them.bid_suits)
        return self._support_for_suits(partners_suits, history)


class Unusual2NShape(Constraint):
    # 5-5 in two lowest unbid suits
    def expr(self, history, call):
        unbid_suits = sorted(list(history.unbid_suits))[:2]
        return z3.And([expr_for_suit(suit) >= 5 for suit in unbid_suits])


class StopperInRHOSuit(Constraint):
    def expr(self, history, call):
        rho_suit = history.rho.last_call.strain
        if rho_suit is None:
            return model.NO_CONSTRAINTS
        return model.stopper_expr_for_suit(rho_suit)


class StoppersInUnbidSuits(Constraint):
    def expr(self, history, call):
        if not history.unbid_suits:
            return model.NO_CONSTRAINTS
        return z3.And([model.stopper_expr_for_suit(suit) for suit in history.unbid_suits])


class StoppersInOpponentsSuits(Constraint):
    def expr(self, history, call):
        if not history.them.bid_suits:
            return model.NO_CONSTRAINTS
        return z3.And([model.stopper_expr_for_suit(suit) for suit in history.them.bid_suits])


class Stopper(Constraint):
    def expr(self, history, call):
        return model.stopper_expr_for_suit(call.strain)


class LongestSuitExceptOpponentSuits(Constraint):
    def expr(self, history, call):
        suit_expr = expr_for_suit(call.strain)
        # Including hearts >= hearts in this And doesn't hurt, but just reads funny when debugging.
        return z3.And([suit_expr >= expr_for_suit(suit) for suit in history.them.unbid_suits if suit != call.strain])


class LongestOfPartnersSuits(Constraint):
    def expr(self, history, call):
        # Nothing to say if partner hasn't bid more than one suit.
        if len(history.partner.bid_suits) < 2:
            return model.NO_CONSTRAINTS
        suit_expr = expr_for_suit(call.strain)
        # Including hearts >= hearts in this And doesn't hurt, but just reads funny when debugging.
        return z3.And([suit_expr >= expr_for_suit(suit) for suit in history.partner.bid_suits if suit != call.strain])


class TwoOfTheTopThree(Constraint):
    def expr(self, history, call):
        return (
            model.two_of_the_top_three_clubs,
            model.two_of_the_top_three_diamonds,
            model.two_of_the_top_three_hearts,
            model.two_of_the_top_three_spades,
        )[call.strain.index]


class ThreeOfTheTopFiveOrBetter(Constraint):
    def __init__(self, suit=None):
        self.suit = suit

    def expr(self, history, call):
        strain = self.suit if self.suit is not None else call.strain
        return (
            model.three_of_the_top_five_clubs_or_better,
            model.three_of_the_top_five_diamonds_or_better,
            model.three_of_the_top_five_hearts_or_better,
            model.three_of_the_top_five_spades_or_better,
        )[strain.index]


class ThirdRoundStopper(Constraint):
    def expr(self, history, call):
        return (
            model.third_round_stopper_clubs,
            model.third_round_stopper_diamonds,
            model.third_round_stopper_hearts,
            model.third_round_stopper_spades,
        )[call.strain.index]


class OpeningRuleConstraint(Constraint):
    def expr(self, history, call):
        if history.rho.last_call is None or history.partner.last_call is None or history.lho.last_call is None:
            return model.rule_of_twenty
        # FIXME: We play rule-of-nineteen, but it's inconsistent with some test cases
        # if history.lho.last_call is None:
        #    return model.rule_of_nineteen
        return model.rule_of_fifteen


class MinCombinedPointsForPartnerMinimumSuitedRebid(Constraint):
    def expr(self, history, call):
        # If we're forcing partner to bid, we're promising it's OK to rebid their suit at the next level with a minimum.
        partner_call = history.partner.last_call
        assert call.strain != partner_call.strain
        rebid_level = call.level
        if call.strain > partner_call.strain:
            rebid_level += 1
        # NOTE: This math matches NaturalSuited (almost):
        expected_points = 19 + (rebid_level - 2) * 3
        return model.points >= expected_points - history.partner.min_points
