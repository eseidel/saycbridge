# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b.model import expr_for_suit
import z3b.model as model
import z3


class Constraint(object):
    def expr(self, history, call):
        raise NotImplementedError


class ConstraintOr(Constraint):
    def __init__(self, *constraints):
        self.constraints = constraints

    def expr(self, history, call):
        return z3.Or([constraint.expr(history, call) if isinstance(constraint, Constraint) else constraint for constraint in self.constraints])


class MinimumCombinedLength(Constraint):
    def __init__(self, min_count):
        self.min_count = min_count

    def expr(self, history, call):
        suit = call.strain
        partner_promised_length = history.partner.min_length(suit)
        implied_length = max(self.min_count - partner_promised_length, 0)
        return expr_for_suit(suit) >= implied_length


class MinimumCombinedPoints(Constraint):
    def __init__(self, min_points):
        self.min_points = min_points

    def expr(self, history, call):
        return model.points >= max(0, self.min_points - history.partner.min_points)


class MinLength(Constraint):
    def __init__(self, min_length):
        self.min_length = min_length

    def expr(self, history, call):
        return expr_for_suit(call.strain) >= self.min_length


class MaxLength(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def expr(self, history, call):
        return expr_for_suit(call.strain) <= self.max_length


class LengthSatisfiesLawOfTotalTricks(Constraint):
    def expr(self, history, call):
        # Written forward: level = partner_min + my_min - 6
        my_count = call.level() + 6 - history.partner.min_length(call.strain)
        return expr_for_suit(call.strain) >= my_count


class SupportForPartnerLastBid(Constraint):
    def __init__(self, min_count):
        self._min_count = min_count

    def expr(self, history, call):
        partner_suit = history.partner.last_call.strain
        return expr_for_suit(partner_suit) >= self._min_count


class SupportForUnbidSuits(Constraint):
    def _four_in_almost_every_suit(self, missing_suit, suits):
        return z3.And([expr_for_suit(suit) >= 4 for suit in set(suits) - set([missing_suit])])

    def expr(self, history, call):
        unbid_suits = history.unbid_suits
        if len(unbid_suits) == 3:
            three_card_support_expr = z3.And([expr_for_suit(suit) >= 3 for suit in unbid_suits])
            four_card_support_expr = z3.Or([self._four_in_almost_every_suit(missing_suit, unbid_suits) for missing_suit in unbid_suits])
            return z3.And(three_card_support_expr, four_card_support_expr)
        if len(unbid_suits) == 2:
            return z3.And([expr_for_suit(suit) >= 4 for suit in unbid_suits])
        assert False, "SupportForUnbidSuits only supports 2 or 3 unbid suits."


class TwoOfTheTopThree(Constraint):
    def expr(self, history, call):
        return (
            model.two_of_the_top_three_clubs,
            model.two_of_the_top_three_diamonds,
            model.two_of_the_top_three_hearts,
            model.two_of_the_top_three_spades,
        )[call.strain]


class ThreeOfTheTopFive(Constraint):
    def expr(self, history, call):
        return (
            model.three_of_the_top_five_clubs,
            model.three_of_the_top_five_diamonds,
            model.three_of_the_top_five_hearts,
            model.three_of_the_top_five_spades,
        )[call.strain]


class OpeningRuleConstraint(Constraint):
    def expr(self, history, call):
        if history.rho.last_call is None or history.partner.last_call is None or history.lho.last_call is None:
            return model.rule_of_twenty
        # FIXME: We play rule-of-nineteen, but it's inconsistent with some test cases
        #if history.lho.last_call is None:
        #    return model.rule_of_nineteen
        return model.rule_of_fifteen
