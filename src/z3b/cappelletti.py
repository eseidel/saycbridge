# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b import enum
from z3b.constraints import *
from z3b.model import *
from z3b.preconditions import *
from z3b.rules import *


# Cappalletti may promise < 15 hcp, since 3-level overcalls are also on and may be preferred.
class Cappalletti(Rule):
    preconditions = [
        LastBidHasAnnotation(positions.RHO, annotations.Opening),
        LastBidWas(positions.RHO, '1N'),
    ]
    constraints = {
        '2C': z3.Or(clubs >= 6, diamonds >= 6, hearts >= 6, spades >= 6),
        '2D': z3.And(hearts >= 5, spades >= 5),
        '2H': z3.And(hearts >= 5, z3.Or(clubs >= 5, diamonds >= 5)),
        '2S': z3.And(spades >= 5, z3.Or(clubs >= 5, diamonds >= 5)),
        '2N': z3.And(clubs >= 5, diamonds >= 5),
    }
    annotations_per_call = {
        ('2C', '2D', '2N'): annotations.Artificial
    }
    annotations = annotations.Cappalletti
    # The book suggests "decent strength".
    # The book bids Cappalletti with 11 hcp, but seems to want 12 hcp when responding.
    shared_constraints = points >= 11


rule_order.order(
    DefaultPass,
    Cappalletti,
)


class ResponseToCappalletti(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Cappalletti)


cappalletti_two_club_responses = enum.Enum(
    "StrongSpades",
    "StrongHearts",
    "LongClubs",
    "BalancedWithPoints",
    "Waiting",
)
rule_order.order(*reversed(cappalletti_two_club_responses))


class ResponseToCappallettiTwoClubs(ResponseToCappalletti):
    preconditions = LastBidWas(positions.Partner, '2C')
    constraints = {
        'P':  [(clubs >= 6, ThreeOfTheTopFiveOrBetter(suit.CLUBS)), cappalletti_two_club_responses.LongClubs],
        '2D': [NO_CONSTRAINTS, cappalletti_two_club_responses.Waiting],
        '2H': [(hearts >= 5, ThreeOfTheTopFiveOrBetter()), cappalletti_two_club_responses.StrongHearts],
        '2S': [(spades >= 5, ThreeOfTheTopFiveOrBetter()), cappalletti_two_club_responses.StrongSpades],
        '2N': [(points >= 11, balanced), cappalletti_two_club_responses.BalancedWithPoints],
        # Could 3C be strong long clubs?
        # And 3D be long diamonds?
    }
    annotations_per_call = {
        '2D': annotations.Artificial,
    }


cappalletti_two_diamonds_responses = enum.Enum(
    "InvitationalHeartSupport",
    "InvitationalSpadeSupport",
    "HeartPreference",
    "SpadePreference",
    "LongClubs",
    "LongDiamonds",
    "MinorEscape",
)
rule_order.order(*reversed(cappalletti_two_diamonds_responses))

cappalletti_two_diamonds_invitational_responses = set([
    cappalletti_two_diamonds_responses.InvitationalHeartSupport,
    cappalletti_two_diamonds_responses.InvitationalSpadeSupport,
])

# Law bids (supporting a major) are better than MinorEscape
rule_order.order(cappalletti_two_diamonds_responses.MinorEscape, natural_suited_part_scores)
# We'd rather be invitational to game than just a law bid.
rule_order.order(natural_suited_part_scores, cappalletti_two_diamonds_invitational_responses)


class ResponseToCappallettiTwoDiamonds(ResponseToCappalletti):
    preconditions = LastBidWas(positions.Partner, '2D')
    constraints = {
        'P':  [(diamonds >= 6, ThreeOfTheTopFiveOrBetter(suit.DIAMONDS)), cappalletti_two_diamonds_responses.LongDiamonds],
        '2N': (NO_CONSTRAINTS, cappalletti_two_diamonds_responses.MinorEscape),
        '3C':  [(clubs >= 6, ThreeOfTheTopFiveOrBetter(suit.CLUBS)), cappalletti_two_diamonds_responses.LongClubs],

        # Could these be natural too?  They imply invitational points?  But how many does partner have?
        '3H': [(MinimumCombinedLength(9), MinimumCombinedPoints(22)), cappalletti_two_diamonds_responses.InvitationalHeartSupport], 
        '3S': [(MinimumCombinedLength(9), MinimumCombinedPoints(22)), cappalletti_two_diamonds_responses.InvitationalSpadeSupport],
    }
    annotations_per_call = {
        '2N': annotations.Artificial,
    }


class ResponseToCappallettiTwoDiamonds(ResponseToCappalletti):
    preconditions = LastBidWas(positions.Partner, '2D')
    constraints = {
        'P':  [(diamonds >= 6, ThreeOfTheTopFiveOrBetter(suit.DIAMONDS)), cappalletti_two_diamonds_responses.LongDiamonds],
        '2N': (NO_CONSTRAINTS, cappalletti_two_diamonds_responses.MinorEscape),
        '3C':  [(clubs >= 6, ThreeOfTheTopFiveOrBetter(suit.CLUBS)), cappalletti_two_diamonds_responses.LongClubs],

        # Could these be natural too?  They imply invitational points?  But how many does partner have?
        '3H': [(MinimumCombinedLength(9), MinimumCombinedPoints(22)), cappalletti_two_diamonds_responses.InvitationalHeartSupport], 
        '3S': [(MinimumCombinedLength(9), MinimumCombinedPoints(22)), cappalletti_two_diamonds_responses.InvitationalSpadeSupport],
    }
    annotations_per_call = {
        '2N': annotations.Artificial,
    }


cappalletti_major_raise_responses = enum.Enum(
    "InvitationalHeartSupport",
    "InvitationalSpadeSupport"
)


class RaiseResponseToMajorCappalletti(ResponseToCappalletti):
    preconditions = [
        LastBidHasStrain(positions.Partner, suit.MAJORS),
        RaiseOfPartnersLastSuit(),
    ]
    priorities_per_call = {
        '3H': cappalletti_major_raise_responses.InvitationalHeartSupport, 
        '3S': cappalletti_major_raise_responses.InvitationalSpadeSupport,
    }
    shared_constraints = [
        MinimumCombinedLength(8),
        # Should this be support points?
        MinimumCombinedPoints(18)
    ]

	