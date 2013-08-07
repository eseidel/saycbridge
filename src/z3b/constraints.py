# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b.model import expr_for_suit
import z3b.model as model
import z3


class Constraint(object):
    def expr(self, history, call):
        pass


class ConstraintOr(Constraint):
    def __init__(self, *constraints):
        self.constraints = constraints

    def expr(self, history, call):
        return z3.Or([constraint.expr(history, call) for constraint in self.constraints])


class MinLengthPartnerLastSuit(Constraint):
    def __init__(self, min_length):
        self.min_length = min_length

    def expr(self, history, call):
        suit = history.last_call_for_position(model.positions.Partner).strain
        return expr_for_suit(suit) >= self.min_length


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


class MaximumPoints(Constraint):
    def __init__(self, max_points):
        self.max_points = max_points

    def expr(self, history, call):
        return model.points <= self.max_points

class MinLength(Constraint):
    def __init__(self, min_length):
        self.min_length = min_length

    def expr(self, history, call):
        return expr_for_suit(call.strain) >= self.min_length


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


class ThreeSuitedHand(Constraint):
    def __init__(self, short_suit):
        self.short_suit = short_suit

    def expr(self, history, call):
        return (
            model.three_suited_short_clubs,
            model.three_suited_short_diamonds,
            model.three_suited_short_hearts,
            model.three_suited_short_spades,
        )[self.short_suit]
