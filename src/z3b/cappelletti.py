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
    # playing_points here is sorta compensating for us not using length_points?
    shared_constraints = points >= 10, playing_points >= 12


rule_order.order(
    DefaultPass,
    cappelletti_calls,
    # p112, h14 seems to imply we'd rather preempt than cappelletti when available.
    set([weak_preemptive_overcalls.WeakFourLevel, weak_preemptive_overcalls.WeakThreeLevel]),
)


class ResponseToCappelletti(Rule):
    preconditions = LastBidHasAnnotation(positions.Partner, annotations.Cappelletti)


class PassResponseToOneNotrumpPenaltyDouble(ResponseToCappelletti):
    preconditions = LastBidWas(positions.Partner, 'X')
    constraints = {
        'P': MinimumCombinedPoints(21), # We have a point majority and should penalize 1N.
    }


class NewSuitResponseToOneNotrumpPenaltyDouble(ResponseToCappelletti):
    preconditions = [
        LastBidWas(positions.Partner, 'X'),
        UnbidSuit(),
        NotJumpFromLastContract(),
    ]
    call_names = ['2C', '2D', '2H', '2S']
    shared_constraints = [MinLength(4), LongestSuitExceptOpponentSuits()]


rule_order.order(
    NewSuitResponseToOneNotrumpPenaltyDouble,
    PassResponseToOneNotrumpPenaltyDouble,
)


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


class RebidAfterCappelleti(Rule):
    preconditions = LastBidHasAnnotation(positions.Me, annotations.Cappelletti)



class SuitRebidAfterCappellettiTwoClubs(RebidAfterCappelleti):
    preconditions = [
        LastBidWas(positions.Me, '2C'),
        UnbidSuit(),
    ]
    # FIXME: What if they interfere?
    call_names = ('2H', '2S', '3C', '3D')
    shared_constraints = MinLength(6)



cappelletti_two_diamonds_responses = enum.Enum(
    "InvitationalHeartSupport",
    "InvitationalSpadeSupport",
    "HeartPreference",
    "SpadePreference",
    "BothMinors",
    "LongClubs",
    "LongDiamonds",
)
rule_order.order(*reversed(cappelletti_two_diamonds_responses))

cappelletti_two_diamonds_invitational_responses = set([
    cappelletti_two_diamonds_responses.InvitationalHeartSupport,
    cappelletti_two_diamonds_responses.InvitationalSpadeSupport,
])

# Law bids (supporting a major) are better than BothMinors
rule_order.order(cappelletti_two_diamonds_responses.BothMinors, natural_suited_part_scores)
# We'd rather be invitational to game than just a law bid.
rule_order.order(natural_suited_part_scores, cappelletti_two_diamonds_invitational_responses)


class ResponseToCappellettiTwoDiamonds(ResponseToCappelletti):
    preconditions = LastBidWas(positions.Partner, '2D')
    constraints = {
        'P':  [(diamonds >= 6, ThreeOfTheTopFiveOrBetter(suit.DIAMONDS)), cappelletti_two_diamonds_responses.LongDiamonds],
        # Partner has already said he's 5-5 in the majors, so he has at most 3 in the minors.
        '2N': [(clubs >= 5, diamonds >= 5), cappelletti_two_diamonds_responses.BothMinors],
        '3C': [(clubs >= 6, ThreeOfTheTopFiveOrBetter(suit.CLUBS)), cappelletti_two_diamonds_responses.LongClubs],

        # Could these be natural too?  They imply invitational points?  But how many does partner have?
        # Currently we're assuming that 2D promises 5-5 in the majors.
        '3H': [(MinimumCombinedLength(9), MinimumCombinedSupportPoints(22)), cappelletti_two_diamonds_responses.InvitationalHeartSupport],
        '3S': [(MinimumCombinedLength(9), MinimumCombinedSupportPoints(22)), cappelletti_two_diamonds_responses.InvitationalSpadeSupport],
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


class ResponseToMajorCappelletti(ResponseToCappelletti):
    preconditions = LastBidHasStrain(positions.Partner, suit.MAJORS)


class NewSuitResponseToMajorCappelletti(ResponseToMajorCappelletti):
    preconditions = UnbidSuit()
    call_names = ('2S', '3C', '3D', '3H')
    shared_constraints = [
        MinLength(6),
        ThreeOfTheTopFiveOrBetter(),
    ]


class RaiseResponseToMajorCappelletti(ResponseToMajorCappelletti):
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
        # Partner could have as few as 10 points!
        MinimumCombinedPoints(18)
    ]


rule_order.order(
    DefaultPass,
    NewSuitResponseToMajorCappelletti,
    cappelletti_major_raise_responses,
)


class CappellettiMinorRequest(ResponseToMajorCappelletti):
    call_names = '2N'
    requires_planning = True # FIXME: Can't we do this with constraints?
    annotations = annotations.CappellettiMinorRequest
    shared_constraints = NO_CONSTRAINTS


class ResponseToCappellettiMinorRequest(RebidAfterCappelleti):
    preconditions = [
        NotJumpFromLastContract(),
        LastBidHasAnnotation(positions.Partner, annotations.CappellettiMinorRequest),
    ]
    call_names = ('3C', '3D')
    shared_constraints = MinLength(5)


class RaiseAfterCappellettiMinorRequest(Rule):
    preconditions = [
        LastBidHasAnnotation(positions.Me, annotations.CappellettiMinorRequest),
        PartnerHasAtLeastLengthInSuit(5),
    ]
    call_names = ('3H', '3S')
    shared_constraints = [
        MinimumCombinedLength(8),
        MinimumCombinedSupportPoints(22), # Matches limit raise
    ]

rule_order.order(
    DefaultPass,
    RaiseAfterCappellettiMinorRequest,
)
