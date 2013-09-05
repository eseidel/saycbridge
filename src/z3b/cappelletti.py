# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b import enum
from z3b.constraints import *
from z3b.model import *
from z3b.preconditions import *
from z3b.rules import *


cappelletti_calls = enum.Enum(
    "PenaltyDouble",
    "TwoSuits",
    "LongSuit",
)
rule_order.order(*reversed(cappelletti_calls))


# Cappelletti may promise < 15 hcp, since 3-level overcalls are also on and may be preferred.
class Cappelletti(Rule):
    preconditions = [
        LastBidHasAnnotation(positions.RHO, annotations.Opening),
        LastBidWas(positions.RHO, '1N'),
    ]
    constraints = {
        '2C': [z3.Or(clubs >= 6, diamonds >= 6, hearts >= 6, spades >= 6), cappelletti_calls.LongSuit],
        '2D': [z3.And(hearts >= 5, spades >= 5), cappelletti_calls.TwoSuits],
        '2H': [z3.And(hearts >= 5, z3.Or(clubs >= 5, diamonds >= 5)), cappelletti_calls.TwoSuits],
        '2S': [z3.And(spades >= 5, z3.Or(clubs >= 5, diamonds >= 5)), cappelletti_calls.TwoSuits],
        '2N': [z3.And(clubs >= 5, diamonds >= 5), cappelletti_calls.TwoSuits],
        # I think the logic here is that with such an uneven distribution of points
        # in the opponents, we don't really want to play a game anyway, so we just penalize them.
        'X': [points >= 15, cappelletti_calls.PenaltyDouble],
    }
    annotations_per_call = {
        ('2C', '2D', '2N'): annotations.Artificial
    }
    annotations = annotations.Cappelletti
    # The book suggests "decent strength".
    # The book bids Cappelletti with 11 hcp, but seems to want 12 hcp when responding.
    # Wikipedia says Cappelletti is 9-14 hcp.
    shared_constraints = points >= 10


rule_order.order(
    DefaultPass,
    cappelletti_calls,
)


class ResponseToCappelletti(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Cappelletti)


cappelletti_two_club_responses = enum.Enum(
    "StrongSpades",
    "StrongHearts",
    "LongClubs",
    "BalancedWithPoints",
    "Waiting",
)
rule_order.order(*reversed(cappelletti_two_club_responses))


class ResponseToCappellettiTwoClubs(ResponseToCappelletti):
    preconditions = LastBidWas(positions.Partner, '2C')
    constraints = {
        'P':  [(clubs >= 6, ThreeOfTheTopFiveOrBetter(suit.CLUBS)), cappelletti_two_club_responses.LongClubs],
        '2D': [NO_CONSTRAINTS, cappelletti_two_club_responses.Waiting],
        '2H': [(hearts >= 5, ThreeOfTheTopFiveOrBetter()), cappelletti_two_club_responses.StrongHearts],
        '2S': [(spades >= 5, ThreeOfTheTopFiveOrBetter()), cappelletti_two_club_responses.StrongSpades],
        '2N': [(points >= 11, balanced), cappelletti_two_club_responses.BalancedWithPoints],
        # Could 3C be strong long clubs?
        # And 3D be long diamonds?
    }
    annotations_per_call = {
        '2D': annotations.Artificial,
    }


cappelletti_two_diamonds_responses = enum.Enum(
    "InvitationalHeartSupport",
    "InvitationalSpadeSupport",
    "HeartPreference",
    "SpadePreference",
    "LongClubs",
    "LongDiamonds",
    "MinorEscape",
)
rule_order.order(*reversed(cappelletti_two_diamonds_responses))

cappelletti_two_diamonds_invitational_responses = set([
    cappelletti_two_diamonds_responses.InvitationalHeartSupport,
    cappelletti_two_diamonds_responses.InvitationalSpadeSupport,
])

# Law bids (supporting a major) are better than MinorEscape
rule_order.order(cappelletti_two_diamonds_responses.MinorEscape, natural_suited_part_scores)
# We'd rather be invitational to game than just a law bid.
rule_order.order(natural_suited_part_scores, cappelletti_two_diamonds_invitational_responses)


class ResponseToCappellettiTwoDiamonds(ResponseToCappelletti):
    preconditions = LastBidWas(positions.Partner, '2D')
    constraints = {
        'P':  [(diamonds >= 6, ThreeOfTheTopFiveOrBetter(suit.DIAMONDS)), cappelletti_two_diamonds_responses.LongDiamonds],
        '2N': (NO_CONSTRAINTS, cappelletti_two_diamonds_responses.MinorEscape),
        '3C':  [(clubs >= 6, ThreeOfTheTopFiveOrBetter(suit.CLUBS)), cappelletti_two_diamonds_responses.LongClubs],

        # Could these be natural too?  They imply invitational points?  But how many does partner have?
        '3H': [(MinimumCombinedLength(9), MinimumCombinedPoints(22)), cappelletti_two_diamonds_responses.InvitationalHeartSupport], 
        '3S': [(MinimumCombinedLength(9), MinimumCombinedPoints(22)), cappelletti_two_diamonds_responses.InvitationalSpadeSupport],
    }
    annotations_per_call = {
        '2N': annotations.Artificial,
    }


cappelletti_major_raise_responses = enum.Enum(
    "InvitationalHeartSupport",
    "InvitationalSpadeSupport"
)

rule_order.order(
    DefaultPass,
    cappelletti_major_raise_responses,
)


class RaiseResponseToMajorCappelletti(ResponseToCappelletti):
    preconditions = [
        LastBidHasStrain(positions.Partner, suit.MAJORS),
        RaiseOfPartnersLastSuit(),
    ]
    priorities_per_call = {
        '3H': cappelletti_major_raise_responses.InvitationalHeartSupport, 
        '3S': cappelletti_major_raise_responses.InvitationalSpadeSupport,
    }
    shared_constraints = [
        MinimumCombinedLength(8),
        # Should this be support points?
        MinimumCombinedPoints(18)
    ]

	