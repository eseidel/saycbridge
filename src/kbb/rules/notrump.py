# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from kbb.bidding_priorities import priorities
from kbb.constraints import *
from kbb.handconstraints import HonorConstraint, HandConstraints
from kbb.knowledge import point_systems
from kbb.preconditions import *
from kbb.rules.base import *
from kbb.rules.suited import OpenerRebidAfterStrongTwoClubs
from kbb import semanticbids


import logging
_log = logging.getLogger(__name__)


class NotrumpOpen(Opening):
    priority = priorities.NotrumpOpen
    implied_constraints = {
        '1N': [HighCardPointRange(15, 17)],
        '2N': [HighCardPointRange(20, 21)],
        '3N': [HighCardPointRange(25, 27)],
    }
    shared_implied_constraints = Opening.shared_implied_constraints + [Balanced(), SetNotrumpProtocol()]


class NotrumpJumpRebid(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [JumpFromLastContract(exact_size=1), MaxLevel(2)]
    priority = priorities.NotrumpJumpRebid
    implied_constraints = {
        # We used to assert that this bid showed at most 3 cards in both majors, but:
        # 1H P 1S P 2N can have 5 hearts (but at most 3 spades and could have 4 card minors)
        # 1H 1S P P 2N can have 4 spades and has at least 5 hearts.
        # 1D P 1S P 2N can have at most 3 hearts and 2 spades (otherwise we'd reverse or support partner).
        '2N': [
            HighCardPointRange(18, 19),
            StoppersInOpponentsSuits(),
            Balanced(), # FIXME :Given the second example (5-4 in the majors), this may not mean Balanced!
            # Note: This is not quite LessThanFourCardsInAllSkippedSuits
            # as we can have 4 card minors and choose not to bid them.
            # MaximumLengthInSuitsOtherThanMyLast isn't quite strong enough,
            # but it's better than nothing.
            MaximumLengthInSuitsOtherThanMyLast(4),
            NoFit(),
            MaxLengthForAnySuit(5), # This is redundant with Balanced, but Balanced is wrong and should be removed.
        ]
        # FIXME: It's unclear what a JumpRebid to 3N shows, so only covering 2N for now.
    }


class NotrumpRebidOverTwoClubs(OpenerRebidAfterStrongTwoClubs):
    semantic_bid_class = semanticbids.Opening
    # These bids are only systematic after a 2D response from partner.
    preconditions = OpenerRebidAfterStrongTwoClubs.preconditions + [PartnerLastBidWasWaiting()]
    implied_constraints = {
        '2N': [HighCardPointRange(22, 24)],
        '3N': [HighCardPointRange(25, 27)],
    }
    # Unclear what these say about majors.  But Stayman is on over them, so that may be sufficient.
    # NoMajorFit() should imply that we don't have a MajorFit on our own w/o help from partner.
    shared_implied_constraints = OpenerRebid.shared_implied_constraints + [NoMajorFit(), Balanced(), SetNotrumpProtocol()]
    # FIXME: Perhaps this needs to be higher priority than OpenerRebidAfterNegativeResponseToTwoClubs?
    # We might also have a 5 card major when bidding this, as per board 5-76b7d2139c43e8338969471cea


class NotrumpGameInvitation(Rule):
    # This is an explicit descriptive rule, not a ToPlay rule.
    # ToPlay is 7-9, but 7 points isn't in game range.
    preconditions = Rule.preconditions + [PartnerLastBidWasOpen(), IsNotrumpProtocol(), PartnerLastBidWasNaturalNotrump()]
    point_system = point_systems.NotrumpSupport
    implied_constraints = {
        '2N': [HighCardPointRange(8, 9)],
    }


class ResponseToNotrumpOpen(Rule):
    # Systems are on after RHO pass, Double or 2C.  However X replaces 2C if RHO overcalled 2C.
    preconditions = Rule.preconditions + [PartnerLastBidWasOpen(), IsNotrumpProtocol(), PartnerLastBidWasNaturalNotrump()]


class Stayman(object):
    # Stayman can be bid for 3 different reasons, but always implies the same.
    # - invitationally, as it implies (8+hcp, 4-card major)
    # - an escape <8 points, no fewer than 4 diamonds, or 3 of either major.
    # - to allow a game-forcing minor jump.
    preconditions = [NotJumpFromPartnerLastBid()]
    priority = priorities.Stayman
    implied_constraints = {
        '2C': [MinimumCombinedPoints(23)], # 8+ over 1N (at least invitational to game, 15 + 8 = 23 thus bailing in 2N is safe)
        '3C': [MinimumCombinedPoints(25)], # 5+ over 2N or 3+ over 2N rebid over 2C (20 + 5 or 22 + 3 = 25 thus bailing to 3N is safe)
        # FIXME: The range for 4C is wrong here!  2C P 2D P 3N shows at least 25+?  Possibly 28+!
        '4C': [MinimumCombinedPoints(27)], # 5+ over 3N (22 + 5 = 27, thus bailing to 4N is safe)
    }
    shared_implied_constraints = [MaxLength(5, SPADES), MaxLength(5, HEARTS)]
    semantic_bid_class = semanticbids.Stayman
    explanation = "Stayman is used to find a 4-4 major fit.  It indicates invitational-or-better points."


class StaymanNoCompetition(Stayman, ResponseToNotrumpOpen):
    preconditions = ResponseToNotrumpOpen.preconditions + Stayman.preconditions + [RHOPassed()]


class StaymanAfterRHODouble(Stayman, ResponseToNotrumpOpen):
    preconditions = ResponseToNotrumpOpen.preconditions + Stayman.preconditions + [RHODoubled()]


class StaymanAfterRHOClubOvercall(Stayman, ResponseToNotrumpOpen):
    # FIXME: If RHO preempts 3C over 1N and we double, is that stayman?
    preconditions = ResponseToNotrumpOpen.preconditions + Stayman.preconditions + [RHOBidContract(), LastBidWasSuit(in_suits=[CLUBS])]
    implied_constraints = {
        # FIXME: MinCombinedPointsForPartnerMinimumRebid only makes it 7+ over 1N, should be 8+!
        'X': [MinCombinedPointsForPartnerMinimumRebid()],
    }


# FIXME: Need StaymanCuebid for when we cuebid RHO's diamond/heart/spade bid.


class ResponseToStayman(Rule):
    # FIXME: This should require RHOPassed, and then have explicit rules for cases where RHO did not pass.
    preconditions = Rule.preconditions + [PartnerLastBidWasStayman(), NotJumpFromPartnerLastBid()]
    implied_constraints = {
        Rule.DIAMONDS: [MaxLength(3, HEARTS), MaxLength(3, SPADES)],
        Rule.HEARTS: [MinLength(4, HEARTS)],
        # Spades denies hearts since it's possible to be 4-4 and balanced, but not 5-4.
        Rule.SPADES: [MaxLength(3, HEARTS), MinLength(4, SPADES)],
    }

    def semantic_bid(self, bid):
        # Diamond response to stayman is artificial.  Responder could have only 2 diamonds.
        if bid.strain == DIAMONDS:
            bid_class = semanticbids.Artificial
        else:
            bid_class = semanticbids.SemanticBid
        return bid_class(bid.name)


# FIXME: Feels like we should have a better way to do this.
class DisallowAllStaymanResponses(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasStayman()]
    def consume_call(self, knowledge, call):
        return None


class RebidAfterStayman(Rule):
    preconditions = [MyLastBidWasStayman()]


class RebidAfterStaymanOverOneNotrump(Rule):
    preconditions = RebidAfterStayman.preconditions + [MyLastBidWas('2C')]


class GarbageStaymanPass(RebidAfterStaymanOverOneNotrump):
    implied_constraints = {
        'P': [
            ForgetEverythingAboutMe(),  # FIXME: We only want to forget the previous point range.
            MaxHighCardPoints(7),
            MinLength(4, DIAMONDS),
            MinLength(3, HEARTS),
            MinLength(3, SPADES),
            # With a 4-card major we would have transfered to it instead.
            MaxLength(4, HEARTS),
            MaxLength(4, SPADES),
        ]
    }
    explanation = "An abuse of the Stayman convention to escape to a 7-card fit in a 2-level contract."


class MinorGameForceRebid(RebidAfterStaymanOverOneNotrump):
    implied_constraints = {
        '3C': [ForgetEverythingAboutMe(), MinLength(6), MinHighCardPoints(13)],
        '3D': [ForgetEverythingAboutMe(), MinLength(6), MinHighCardPoints(13)],
    }
    priority = priorities.MinorGameForceRebidAfterStayman


class NotrumpRebidAfterStayman(RebidAfterStayman):
    # Should deny major fit with his partner.
    # Should indicate exactly 4 in the unbid major.
    implied_constraints = {
        '2N': [HighCardPointRange(8, 9)],
        # Use MinimumCombinedPoints so that it works over 3C stayman responses too.
        # Note: We allow up to 30 points (when jumping) as 5N is Quantitative5N, and our key to slam.
        '3N': [CombinedPointRangeOverPartnerMinimum(25, 30)],
    }
    point_system = point_systems.NotrumpSupport
    shared_implied_constraints = RebidAfterStayman.shared_implied_constraints + [
        NoMajorFit(), # We don't have 4 of the major partner bid.
        LengthInOtherMajor(4),  # But we definitely have 4 of the other one, if partner bid a major.
        # Otherwise, we definitely promised 4 in one of the majors, and don't have more than 4 in either.
        MaxLength(4, HEARTS),
        MaxLength(4, SPADES)
    ]


class OtherMajorRebidAfterStayman(RebidAfterStayman):
    preconditions = RebidAfterStayman.preconditions + [NotRaiseOfPartnersLastSuit()]
    # Rebidding the other major shows 5-4, with invitational or game-force values.
    implied_constraints = {
        '2H': [HighCardPointRange(8, 9), Length(5), Length(4, SPADES)],
        '2S': [HighCardPointRange(8, 9), Length(5), Length(4, HEARTS)],

        # Use MinimumCombinedPoints instead of MinHighCardPoints as 3-level bids
        # are game forcing over both 2C and 3C Stayman responses.
        '3H': [MinimumCombinedPoints(25), Length(5), Length(4, SPADES)],
        '3S': [MinimumCombinedPoints(25), Length(5), Length(4, HEARTS)],
    }


class JacobyTransfer(object):
    # Transfers make sense over 1, 2, 3NT
    preconditions = ResponseToNotrumpOpen.preconditions + [IsSuit(), NotJumpFromPartnerLastBid(), MaxLevel(4)]

    implied_constraints = {
        Rule.DIAMONDS: [MinLength(5, HEARTS)],
        Rule.HEARTS: [MinLength(5, SPADES)],
    }

    def _implied_suit(self, transfer_suit):
        return {
            DIAMONDS: HEARTS,
            HEARTS: SPADES,
        }.get(transfer_suit)

    def semantic_bid(self, bid):
        return semanticbids.JacobyTransfer(bid.name, transfer_to=self._implied_suit(bid.strain))

    def _preferred_major_for_hand(self, hand):
        # Always bid the longer major first, regardless of points?
        if hand.length_of_suit(SPADES) > hand.length_of_suit(HEARTS):
            return SPADES
        elif hand.length_of_suit(SPADES) < hand.length_of_suit(HEARTS):
            return HEARTS

        if hand.high_card_points() < 8:
            # We're not going to game, prefer bidding our better major.
            if hand.hcp_in_suit(HEARTS) > hand.hcp_in_suit(SPADES):
                return HEARTS
            else:
                return SPADES
        elif hand.high_card_points() in (8, 9):
            # With invitational values, start with hearts and rebid spades.
            return HEARTS
        # With game forcing values and 5-5 or better, start with spades.
        return SPADES

    def priority_for_bid(self, hand, bid):
        if self._implied_suit(bid.strain) == self._preferred_major_for_hand(hand):
            return priorities.JacobyTransferToBetterMajor
        return priorities.JacobyTransfer


class JacobyTransferNoCompetition(JacobyTransfer, ResponseToNotrumpOpen):
    preconditions = ResponseToNotrumpOpen.preconditions + JacobyTransfer.preconditions + [RHOPassed()]


class JacobyTransferAfterRHODouble(JacobyTransfer, ResponseToNotrumpOpen):
    preconditions = ResponseToNotrumpOpen.preconditions + JacobyTransfer.preconditions + [RHODoubled()]


class JacobyTransferAfterRHOClubOvercall(JacobyTransfer, ResponseToNotrumpOpen):
    preconditions = ResponseToNotrumpOpen.preconditions + JacobyTransfer.preconditions + [RHOBidContract(), LastBidWasSuit(in_suits=[CLUBS])]


class ResponseToJacobyTransfer(Rule):
    # FIXME: Should this require that RHO pased?
    preconditions = Rule.preconditions + [PartnerLastBidWasJacobyTransfer()]

    def _cheapest_level(self, last_call, suit):
        if suit < last_call.strain:
            return last_call.level + 1
        return last_call.level

    def consume_call(self, knowledge, bid):
        if not bid.is_contract():
            return None  # Passing is not an allowed bid.
        partner_bid = knowledge.partner.last_call
        accept_suit = partner_bid.transfer_to
        accept_level = self._cheapest_level(partner_bid, accept_suit)
        level_change = bid.level - accept_level
        if bid.strain != accept_suit or level_change > 1:
            return None  # Any non-accept is a broken bid.
        if level_change == 1:
            if partner_bid.level != 2:
                return None  # Super accepts only apply over 1N, all others are broken bids.
            knowledge.me.set_min_length(accept_suit, 4)
            knowledge.me.set_min_hcp(17)
        # Otherwise accepting says nothing about the responder.
        return knowledge

    def priority_for_bid(self, hand, bid):
        # FIXME: Maybe these should be separate rules?
        # Unfortunately we can't distinguish these cases using only constraints
        # as one does a normal accept when one has fewer than 4 OR fewer than 17 points.
        if bid.level == 3:
            return priorities.SuperAcceptResponseToJacobyTransfer
        return priorities.ResponseToJacobyTransfer


class RebidAfterJacobyTransfer(Rule):
    # If partner didn't accept the transfer, these rules can't apply.
    preconditions = Rule.preconditions + [MyLastBidWasJacobyTransfer(), PartnerLastBidWasNaturalMajor()]


# Normal suited rebids are handled by SuitedToPlay.
class NotrumpRebidAfterJacobyTransfer(RebidAfterJacobyTransfer):
    implied_constraints = {
        '2N': [HighCardPointRange(8, 9)],
        # Using CombinedPointRangeOverPartnerMinimum to allow this to work after transfers over 2N.
        # 3N and higher imply and no other 5 card suit, as we would have used NewMinorRebidAfterJacobyTransfer instead.
        # FIXME: If we change NewMinorRebidAfterJacobyTransfer to show only 4, then these maxes change to 3.
        '3N': [CombinedPointRangeOverPartnerMinimum(25, 30), MaxLength(4, CLUBS), MaxLength(4, DIAMONDS)],
        # 4N is Blackwood.
        # Higher Notrumps are natural.
    }
    # This does not imply balanced, but rather exactly 5 cards in the transfered suit.
    # 3N and higher imply and no other 5 card suit, as we would have used NewMinorRebidAfterJacobyTransfer instead.
    shared_implied_constraints = RebidAfterJacobyTransfer.shared_implied_constraints + [
        MaximumLengthInPartnerLastBidSuit(5),
        MaximumLengthInOtherMajor(3),  # With 4 we would have used stayman, with 5+ we would have bid OtherMajorRebidAfterJacobyTransfer.
    ]


class OtherMajorRebidAfterJacobyTransfer(RebidAfterJacobyTransfer):
    preconditions = RebidAfterJacobyTransfer.preconditions + [UnbidSuit()]
    # Rebidding the other major shows 5-5 or better in the majors, with invitational or game-force values.
    point_system = point_systems.LengthPoints
    implied_constraints = {
        '2S': [HighCardPointRange(8, 9), MinLength(5)],

        # 3H rebid after 2S shows 5-5 or better in the majors and slam interest.
        '3H': [MinimumCombinedPoints(30)],  # FIXME: Unclear what point range "slam interest" means.

        # 3S rebid over 2H is possible under competition or after a super-accept.
        '3S': [MinimumCombinedPoints(25)],

        # 4H shows no interest in slam, offers choice of game contracts.
        '4H': [CombinedPointRangeOverPartnerMinimum(25, 29)],  # FIXME: Unclear what "no interest in slam" means for points.
    }
    shared_implied_constraints = RebidAfterJacobyTransfer.shared_implied_constraints + [MinLength(5)]


class NewMinorRebidAfterJacobyTransfer(RebidAfterJacobyTransfer):
    implied_constraints = {
        # Minors are not worth mentioning after a jacoby transfer unless we have 5 of them and game-going values.
        # FIXME: It seems like this should imply some number of honors in the bid suit, but there may be times
        # when we have 5+ spot cards in a minor and this looks better than bidding 3N.
        '3C': [MinLength(5), MinimumCombinedPoints(25)],
        '3D': [MinLength(5), MinimumCombinedPoints(25)],
    }


# FIXME: Subclasses of this rule likely do not want the RHOPassed() precondition!
class NotrumpSystemsOnOverOneNotrump(ResponseToNotrumpOpen):
    preconditions = ResponseToNotrumpOpen.preconditions + [PartnerLastBidWas('1N'), RHOPassed()]


class TwoSpadesPuppet(NotrumpSystemsOnOverOneNotrump):
    implied_constraints = {
        # FIXME: This also denies entries in side suits.
        # It's possible 7 points is too much if it's a self-supporting suit.
        # The _have_shape_for_two_spades_puppet in the bidder enforces 6+ in one minor.
        '2S': [HighCardPointRange(0, 7)]
    }
    semantic_bid_class = semanticbids.TwoSpadesPuppet


# FIXME: Need RedoubleTransferToMinor.


class ResponseToTwoSpadesPuppet(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasTwoSpadesPuppet()]
    semantic_bid_class = semanticbids.Artificial  # Should this be artificial?  Should a double be lead-directing?

    def consume_call(self, knowledge, bid):
        assert knowledge.partner.last_call.transfer_to == CLUBS
        assert knowledge.partner.last_call.name == '2S'

        if bid.name != '3C':
            return None
        return knowledge


class ResponseToTwoSpadesPuppetTransferAccept(Rule):
    preconditions = Rule.preconditions + [MyLastBidWasTwoSpadesPuppet()]

    def consume_call(self, knowledge, bid):
        if bid.name not in ('P', '3D'):
            return None
        if bid.name == 'P':
            knowledge.me.set_min_length(CLUBS, 6)
        elif bid.name == '3D':
            knowledge.me.set_min_length(DIAMONDS, 6)
        return knowledge


class LongMinorGameInvitation(NotrumpSystemsOnOverOneNotrump):
    implied_constraints = {
        # FIXME: These also imply no outside entries.
        # FIXME: These imply at least 5 points and less than 10?
        '3C': [MinLength(6), MinHonors(HonorConstraint.TWO_OF_TOP_THREE)],
        '3D': [MinLength(6), MinHonors(HonorConstraint.TWO_OF_TOP_THREE)],
    }
    shared_implied_constraints = NotrumpSystemsOnOverOneNotrump.shared_implied_constraints + [HighCardPointRange(5, 9)]


class LongMajorSlamInvitation(NotrumpSystemsOnOverOneNotrump):
    # Implies 6+ in a major, with 2 of the top 3 and 14+? hcps (p14).
    priority = priorities.LongMajorSlamInvitiation
    implied_constraints = {
        '3H': [MinLength(6), MinHonors(HonorConstraint.TWO_OF_TOP_THREE)],
        '3S': [MinLength(6), MinHonors(HonorConstraint.TWO_OF_TOP_THREE)],
    }
    shared_implied_constraints = NotrumpSystemsOnOverOneNotrump.shared_implied_constraints + [MinHighCardPoints(14)]


class QuantitativeFiveNotrumpJump(Rule):
    preconditions = [PartnerOpened(), IsNotrumpProtocol(), JumpFromLastContract()]
    priority = priorities.QuantitativeFiveNotrump

    def consume_call(self, knowledge, bid):
        if bid.name != '5N':
            return False
        knowledge.me.set_min_hcp(33 - knowledge.partner.max_hcp())
        knowledge.me.set_max_hcp(33 - knowledge.partner.min_hcp() - 1)
        return knowledge


class QuantitativeFourNotrumpJump(ResponseToNotrumpOpen):
    # FIXME: Does this need to be a jump from last contract?
    # If RHO bids at the 4 level, is 4N still quantitative?
    priority = priorities.QuantitativeFourNotrump
    # This only applies in Notrump auctions.
    # Implies min(my_hcp) >= 33 - max(opener_hcp)
    # Implies max(my_hcp) < 33 - min(opener_hcp)
    # Invites opener to bid 6N if at a maxium, otherwise pass.
    def consume_call(self, knowledge, bid):
        if bid.name != '4N':
            return False
        knowledge.me.set_min_hcp(33 - knowledge.partner.max_hcp())
        knowledge.me.set_max_hcp(33 - knowledge.partner.min_hcp() - 1)
        return knowledge
