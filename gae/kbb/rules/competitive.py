# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from kbb.bidding_priorities import priorities
from kbb.constraints import *
from kbb.handconstraints import HonorConstraint, HandConstraints
from kbb.knowledge import point_systems
from kbb.preconditions import *
from kbb.rules.base import *
from kbb import semanticbids


import logging
_log = logging.getLogger(__name__)


### Direct Overcalls ###


class DirectOvercall(Rule):
    # Our first bid, partner may have passed, rho opened.
    # FIXME: PartnerNotOpened is a hack to compensate for the fact that 1N overcalls pretend to be "openings".
    preconditions = Rule.preconditions + [RHOLastBidWasOpen(), PartnerNotOpened()]
    priority = priorities.DirectOvercall


class IndirectOvercall(Rule):
    # Our partner passed, but we haven't bid.  This is not the balancing seat.
    preconditions = Rule.preconditions + [LHOLastBidWasOpen(), PartnerLastBidWas('P'), RHOBidContract(), PartnerNotOpened(), NotOpened()]


class DelayedOvercall(Rule):
    # We passed previously, but this is not the balancing seat (rho bid).
    preconditions = Rule.preconditions + [LHOLastBidWasOpen(), MyLastBidWas('P'), PartnerLastBidWas('P'), RHOBidContract(), PartnerNotOpened()]
    priority = priorities.DirectOvercall


class OvercallPass(object):
    priority = priorities.Pass
    implied_constraints = {
        # 17+ and we would have doubled, unclear what else we can conclude.
        'P': [MaxHighCardPoints(16)],
    }
    explanation = "Could have up to 16 points, but no overcallable suit or strength in opponents' suit(s).  With 17+ points would have doubled."


class DirectOvercallPass(OvercallPass, DirectOvercall):
    pass


class IndirectOvercallPass(OvercallPass, IndirectOvercall):
    pass


class NotrumpOvercall(object):
    priority = priorities.NotrumpOvercall
    semantic_bid_class = semanticbids.Opening  # FIXME: This is a hack to make NT Systems on.
    implied_constraints = {
        '1N': [
            # Overcalling 1N, can be up to 18hcp.
            HighCardPointRange(15, 18),
            Balanced(),
            SetNotrumpProtocol(),
            StoppersInOpponentsSuits(),
            # FIXME: It's kinda a hack to set the Opened flag here.
            # This has a corresponding hack in DirectOvercall to prevent them from being on for LHO.
            SetOpened()
        ]
    }


class DirectNotrumpOvercall(NotrumpOvercall, DirectOvercall):
    pass


class IndirectNotrumpOvercall(NotrumpOvercall, IndirectOvercall):
    pass


# Technically a double, but functionally an overcall in many ways.
class DirectNotrumpDouble(DirectOvercall):
    preconditions = DirectOvercall.preconditions + [LastBidWas('1N')]
    implied_constraints = {
        'X': [HighCardPointRange(15, 17), Balanced(), SetNotrumpProtocol()],
    }
    explanation = "Indicates a 1NT opening hand.  NT conventional responses are off.  Responder can pass with enough points to penalize opener, but more likely should escape to a suit fit."


class SuitedOvercall(object):
    preconditions = [IsSuit(), LastBidWasSuit(), NotJumpFromLastContract()]

    # FIXME: Overcalls are capped at 16 points, but with a two-suited hand we aren't
    # supposed to big-hand-double, so we need a way to plan them with more than 16 points.

    # The book (p99) notes to be cautious about overcalling at the 2-level or above when you have
    # length in RHO's suit as you're more likely to be doubled.
    # We use MaximumLengthInLastBidSuit = 5 for 1-level calls, and 3 for 2+ level calls.
    # FIXME: In the indirect seat we should probably avoid having length in either RHO's or LHO's suit.

    implied_constraints = {
        # Note: We do some magic in the planner to allow 1-level overcalls with only four cards in the suit.
        Rule.LEVEL_1: [HighCardPointRange(8, 16), MinLength(5), CouldBeStrongFourCardSuit(), MaximumLengthInLastBidSuit(5)],
        Rule.LEVEL_2: [HighCardPointRange(10, 16), MinLength(5), MaximumLengthInLastBidSuit(3)],
        Rule.LEVEL_3: [HighCardPointRange(13, 16), MinLength(6), MaximumLengthInLastBidSuit(3)],
    }
    shared_implied_constraints = [MinHonors(HonorConstraint.THREE_OF_TOP_FIVE)]


class DirectSuitedOvercall(SuitedOvercall, DirectOvercall):
    preconditions = DirectOvercall.preconditions + SuitedOvercall.preconditions
    shared_implied_constraints = DirectOvercall.shared_implied_constraints + SuitedOvercall.shared_implied_constraints


class IndirectSuitedOvercall(SuitedOvercall, IndirectOvercall):
    preconditions = IndirectOvercall.preconditions + SuitedOvercall.preconditions
    shared_implied_constraints = IndirectOvercall.shared_implied_constraints + SuitedOvercall.shared_implied_constraints


# We actually allow one-level overcalls with four cards in a suit, but we
# treat them as if they implied five cards for one round. When the overcaller
# bids again, this rule kicks in and revises our knowledge to state that they
# might only have four cards.
class CorrectStrongFourCardSuitLength(Rule):
    def apply(self, knowledge, bid):
        for suit in SUITS:
            if knowledge.me.could_be_strong_four_card(suit):
                knowledge.me.overwrite_min_length(suit, 4)
                knowledge.me.clear_could_be_strong_four_card(suit)
        return knowledge, False


### Responses to Direct Overcalls ###


class ResponseToDirectSuitedOvercall(Rule):
    preconditions = Rule.preconditions + [LHOLastBidWasOpen(), PartnerLastBidWasNaturalSuit(), IsSuitedProtocol()]


class RaiseResponseToDirectOvercall(ResponseToDirectSuitedOvercall):
    preconditions = ResponseToDirectSuitedOvercall.preconditions + [RaiseOfPartnersLastSuit(), NotJumpFromLastContract()]
    implied_constraints = {
        # FIXME: This point range should be level-appropriate.
        Rule.ANY_OTHER_BID: [SupportForPartnerLastBid(3), HighCardPointRange(6, 10)],
    }


class JumpRaiseResponseToDirectOvercall(ResponseToDirectSuitedOvercall):
    # FIXME: Should this only be on when RHO Passed?
    preconditions = ResponseToDirectSuitedOvercall.preconditions + [RaiseOfPartnersLastSuit(), JumpFromPartnerLastBid(), GameOrBelow()]
    implied_constraints = {
        # FIXME: This should imply a weak hand.  Unclear how weak.
        Rule.ANY_OTHER_BID: [LengthSatisfiesLawOfTotalTricks()],
    }
    explanation = "Jump raise response to an overcall shows a weak hand with 4+ card support."


class CuebidResponseToDirectOvercall(ResponseToDirectSuitedOvercall):
    preconditions = ResponseToDirectSuitedOvercall.preconditions + [CuebidOfLHOsSuit(), NotJumpFromLastContract(), BelowGame()]
    implied_constraints = {
        Rule.ANY_OTHER_BID: [SupportForPartnerLastBid(3), MinHighCardPoints(11)],
    }
    # FIXME: We should have cue-bid support of a minor lower priority than NewSuit!
    # However right now prioirty_for_bid only takes hand and bid, not knowledge,
    # So we would need a separate rule for minors vs. majors.
    priority = priorities.CuebidResponseToDirecOvercall


### Rebids after Direct Overcalls ###


class NewSuitResponseToOvercall(ResponseToDirectSuitedOvercall):
    preconditions = Rule.preconditions + [TheyOpened(), PartnerLastBidWasContract(), NotJumpFromLastContract(), MaxLevel(3), UnbidSuit()]
    implied_constraints = {
        Rule.ANY_OTHER_BID: [],
    }
    shared_implied_constraints = [
        MinLength(5),
        MinHonors(HonorConstraint.TWO_OF_TOP_THREE),
        # Unclear exactly how many points these should promise, but this seems reasoanble for now.
        MinCombinedPointsForPartnerMinimumRebid(),
    ]


### Balancing Overcalls ###


class BalancingOvercall(Rule):
    # RHO has shown fewer than 5 points, so we assume 2.5 points more in each LHO and Partner and thus steal 3 points from partner.
    # FIXME: Some BalancingOvercalls are on after a previous pass, when both LHO and RHO have bid.
    # When not to balance:
    # - With strong holdings in opponent's suit.
    # - When balancing would allow them to find a better suit.
    # - When values in their suit would be wasted if you are declarer (protected queens/jacks).
    # FIXME: Unclear if this should only apply when LHO opened.  Any time we're in the pass-out seat, we're balancing, no?
    preconditions = Rule.preconditions + [BalancingSeat(), LHOLastBidWasOpen(), LastBidWasSuit()]


class BalancingOvercallNotrump(BalancingOvercall):
    priority = priorities.NotrumpOvercall
    implied_constraints = {
        '1N': [HighCardPointRange(12, 14)],
        '2N': [HighCardPointRange(19, 21)],
    }
    shared_implied_constraints = BalancingOvercall.shared_implied_constraints + [Balanced(), SetNotrumpProtocol(), StoppersInOpponentsSuits()]


class BalancingSuitedOvercall(BalancingOvercall):
    preconditions = BalancingOvercall.preconditions + [IsSuit(), LastBidWasSuit(), NotJumpFromLastContract()]
    implied_constraints = {
        # Unlike DirectSuitedOvercall, we're requiring 5 at the one level.  Unclear if that's correct.
        Rule.LEVEL_1: [HighCardPointRange(5, 13), MinLength(5), MaximumLengthInLastBidSuit(3)],
        Rule.LEVEL_2: [HighCardPointRange(7, 13), MinLength(5), MaximumLengthInLastBidSuit(5)],
        Rule.LEVEL_3: [HighCardPointRange(10, 13), MinLength(6), MaximumLengthInLastBidSuit(5)],
    }
    shared_implied_constraints = BalancingOvercall.shared_implied_constraints + [MinHonors(HonorConstraint.THREE_OF_TOP_FIVE)]
    priority = priorities.BalancingSuitedOvercall


class BalancingJumpOvercall(BalancingOvercall):
    preconditions = BalancingOvercall.preconditions + [IsSuit(), LastBidWasSuit(), JumpFromLastContract(exact_size=1)]
    implied_constraints = {
        # Balancing Jump Overcalls show:
        # - "Opening count" -- currently interpreting this as 12 points (likely 12-16, since otherwise bid-hand double?)
        # - Usually a 6+ card suit (p140, h2)
        Rule.LEVEL_2: [MinHighCardPoints(12), MinLength(6)],
        Rule.LEVEL_3: [MinHighCardPoints(12), MinLength(6)],
    }
    # Should these indicate < 4 in LHO's suit like DirectOvercalls do?
    shared_implied_constraints = BalancingOvercall.shared_implied_constraints + [MaximumLengthInLastBidSuit(3), MinHonors(HonorConstraint.THREE_OF_TOP_FIVE)]
    priority = priorities.BalancingJumpOvercall


### Responses to Balancing Overcalls ###


# FIXME: Do we need a semantic bid to detect partner's balancing overcalls?
# FIXME: Can we generalize our overcall responses to handle all the different kinds of overcalls?


### FourthSeatOvercalls ###


# FIXME: We should be able to overcall after LHO and RHO bid but partner passes.


### Micheals ###


class MichaelsCuebid(object):
    # Mini-Max, meaning 6-10 or 17+ HCP.  Lower priority bid than overcall?
    # Likely should imply the lower range, and then a rebid after michaels implies 17+ (Similar to takeout double)
    # FIXME: Michaels can apply after one pass.
    # FIXME: This is wrong in the case of both 1N P 2D 3D and 1N P 2D 2H.
    # FIXME: Michaels makes sense up to the 4 level, but we really should have more points for 4-level bids.
    preconditions = [IsSuit(), SameSuitAsLastContract(), NotJumpFromLastContract(), MaxLevel(3)]
    semantic_bid_class = semanticbids.MichaelsCuebid
    priority = priorities.MichaelsCuebid
    sayc_page = 103
    explanation = "Shows two 5+ card suits -- either both majors or the unmentioned major and an unspecified minor."

    def consume_call(self, knowledge, bid):
        rho_suit = knowledge.last_contract().strain
        if rho_suit in MINORS:
            promised_suits = MAJORS
        else:
            promised_suits = [SPADES] if rho_suit == HEARTS else [HEARTS]
            # FIXME: We enforce the unspecified minor constraint in the planner,
            # but we have no way to represent it in the knowledge.

        for suit in promised_suits:
            knowledge.me.set_min_length(suit, 5)

        # FIXME: Should a 3-level Michaels should require more points?
        # FIXME: This should be 6-10, and the planner should know how to plan it with 17+ for a "big hand michaels"
        # like how we BigHandDouble.
        knowledge.me.set_min_hcp(6)
        return knowledge


class DirectMichaelsCuebid(MichaelsCuebid, DirectOvercall):
    preconditions = DirectOvercall.preconditions + MichaelsCuebid.preconditions


class BalancingMichaelsCuebid(MichaelsCuebid, BalancingOvercall):
    preconditions = BalancingOvercall.preconditions + MichaelsCuebid.preconditions
    # FIXME: Should this promise fewer points in the balancing seat?


### Responses to Micheals ###

# FIXME: We need to know how to respond to MichaelsCuebid.
# Here's an interesting board to look at: 11-19124908996138856307896841556647-W:NO:

# Responder Bids: (p106 and p108)
# Preference Bid
# Jump Preference (preemptive)
# Cuebid is game or slam try
# New suit (non-forcing)
# 3NT -> ToPlay
# 2NT -> Requests partner to name his minor
# 4C -> Requests partner minor if 2N is not available
# 4N -> Same purpose as 2N or 4C if not available


class ResponseToMichaels(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasMichaels()]


class MichaelsMinorRequest(ResponseToMichaels):
    # FIXME: This only makes sense if partner has shown a minor with his michaels! (i.e. It was a major he cuebid.)
    preconditions = ResponseToMichaels.preconditions + [NotJumpFromLastContract()]
    implied_constraints = {
        '2N': [], # Available when partner's michaels was 2H or 2S.
        '4C': [], # Available when partner's michaels was 3H or 3S or RHO bid at the 3 level.
        '4N': [], # Available when partner's michaels was 4H or 4S or RHO bid at the 4 level.
    }
    # Unclear if this needs to be its own semantic bid, or if the michaels bidder
    # should just interpret the bid based on his last_call and our last_call.
    semantic_bid_class = semanticbids.MichaelsMinorRequest
    priority = priorities.MichaelsMinorRequest
    explanation = "Asks partner to bid his 5-card minor."


class UnforcedMichaelsMinorRequest(MichaelsMinorRequest):
    preconditions = MichaelsMinorRequest.preconditions + [NotForcedToBid()]
    implied_constraints = {
        # FIXME: This should use some MinCombinedPointsForPartnerMinimumRebid variant
        # as a shared_implied_constraint instead.
        '2N': [MinimumCombinedPoints(22)], # Available when partner's michaels was 2H or 2S.
        '4C': [MinimumCombinedPoints(28)], # Available when partner's michaels was 3H or 3S or RHO bid at the 3 level.
        '4N': [MinimumCombinedPoints(28)], # Available when partner's michaels was 4H or 4S or RHO bid at the 4 level.
    }


class ResponseToMichaelsMinorRequest(Rule):
    # FIXME: Should this be on if RHO bid?
    # If RHO bid the other minor is it already obvious which we have?
    # FIXME: If Partner's minor request was 4C and we have clubs, do we just pass?
    preconditions = Rule.preconditions + [PartnerLastBidWasMichaelsMinorRequest(), IsMinor(), MaxLevel(5)]
    shared_implied_constraints = [MinLength(5)]


class NonJumpResponseToMichaelsMinorRequest(ResponseToMichaelsMinorRequest):
    preconditions = ResponseToMichaelsMinorRequest.preconditions + [NotJumpFromLastContract()]
    implied_constraints = {
        # FIXME: This MaxHighCardPoints should be set originally (and probably should be < 10hcp)
        Rule.ANY_OTHER_BID: [MaxHighCardPoints(16)],
    }


# FIXME: Need RebidAfterMichaels, that like RebidAfterTakeoutDouble, shows a strong hand.


class JumpResponseToMichaelsMinorRequest(ResponseToMichaelsMinorRequest):
    preconditions = ResponseToMichaelsMinorRequest.preconditions + [JumpFromLastContract(exact_size=1)]
    implied_constraints = {
        Rule.ANY_OTHER_BID: [MinHighCardPoints(17)],
    }
    shared_implied_constraints = [MinLength(5)]


### Unusual Notrump ###


class UnusualNotrump(DirectOvercall):
    # Implies 5+ cards in the lower two unbid suits.
    # Mini-Max, meaning 6-10 or 17+ HCP.  Lower priority bid than overcall?
    # Likely should imply the lower range, and then a rebid after 2N implies 17+ (Similar to takeout double)
    # FIXME: Need a separate interpretation range from bidding range?
    preconditions = DirectOvercall.preconditions + [LastBidWasSuit(), LastBidWasLevel(1)]
    # FIXME: This should use a dynamic priority for MiniMaxUnusualNotrump?
    # Or should SuitedOvercall just be higher priority always?
    priority = priorities.UnusualNotrump
    semantic_bid_class = semanticbids.UnusualNotrump

    # FIXME: This should instead return the lowest two suits
    # which RHO has not promised any length in.
    def _promised_suits(self, rho_suit):
        if rho_suit in MAJORS:
            return MINORS
        return [DIAMONDS, HEARTS] if rho_suit == CLUBS else [CLUBS, HEARTS]

    def consume_call(self, knowledge, bid):
        if bid.name != '2N':
            return False
        rho_suit = knowledge.rho.last_call.strain
        for suit in self._promised_suits(rho_suit):
            knowledge.me.set_min_length(suit, 5)

        # FIXME: We need a way to specify either 6-10 or 17+.
        # FIXME: Unclear what the top range for Unusual2NT is, if any?
        # p104, h3 may suggest the top range is 20hcp.
        knowledge.me.set_min_hcp(6)
        return knowledge

    explanation = "Shows the 5+ cards in the lower two unbid suits."


class UnusualNotrumpOverTwoClubs(DirectOvercall):
    # FIXME: This could be rolled into the main UnusualNotrump
    # if it were to use suit lengths instead of a manual check.
    preconditions = DirectOvercall.preconditions + [LastBidWas('2C')]
    priority = priorities.UnusualNotrump

    implied_constraints = {
        # 2N over 2C is unusual and promises both minors.
        # FIXME: Unclear what the top of the promised point range is.
        '2N': [MinHighCardPoints(6), MinLength(5, CLUBS), MinLength(5, DIAMONDS)],
    }


class SuperUnusualNotrump(DirectOvercall):
    # FIXME: Per h16 on p107, with 19+ hcp and two 6 card suits, we bid 4N instead of 2N.
    pass


class RebidAfterUnusualNotrump(Rule):
    def apply(self, knowledge, bid):
        if not knowledge.me.last_call or not knowledge.me.last_call.unusual_two_nt:
            return knowledge, False

        if bid.is_pass():
            # FIXME: For mini-max, we shouldn't be bidding UnusualNotrump with more than about 10 points?
            knowledge.me.set_max_hcp(16)
            return knowledge, True

        # For anything other than Pass, we note this was a max Unusual2N but don't consome the bid.
        knowledge.me.set_min_hcp(17)
        return knowledge, False


### Preempts ###


class PreemptiveBid(object):
    # FIXME: Weak N could be made with a bad N+1.
    # FIXME: Should these imply exactly N? or N+?
    preconditions = [IsSuit()]
    implied_constraints = {
        # FIXME: Per p89, 2-level preempts should require no void, and no outside 4-card major.
        # We might even want to say no outside 3-card major?
        '2D': [MinLength(6)],
        '2H': [MinLength(6)],
        '2S': [MinLength(6)],

        # PreemptiveOpen overrides 3C to promise only 6.
        Rule.LEVEL_3: [MinLength(7)],
        Rule.LEVEL_4: [MinLength(8)],

        # Preempt at the 5 level with AKQJxxxx in a minor or KQJxxxxxx?
    }

    # FIXME: It is possible that 2-level preempts should require 2o3 instead of 3o5.
    shared_implied_constraints = [HighCardPointRange(5, 11), MinHonors(HonorConstraint.THREE_OF_TOP_FIVE)]

    def priority_for_bid(cls, hand, bid):
        # Separate the priorties between the levels so we can prefer higher preempts.
        # FIXME: 3rd seat preempts should be higher priority than weak Ro20 openings.
        if bid.level() == 4:
            return priorities.FourLevelPreempt
        if bid.level() == 3:
            return priorities.ThreeLevelPreempt
        assert bid.level() == 2
        return priorities.TwoLevelPreempt


class PreemptiveOpen(PreemptiveBid, Opening):
    # FIXME: This should be NotFourthSeat() not NotBalancingSeat(), or?
    preconditions = Opening.preconditions + PreemptiveBid.preconditions + [NotBalancingSeat()]
    implied_constraints = PreemptiveBid.implied_constraints.copy()
    implied_constraints['3C'] = [MinLength(6)]  # Because 2C is strong, 3C only promises 6 for a preemptive open.

    # FIXME: Need a Constraint/Precondition to avoid preempting when we have possible support for partner's major.
    shared_implied_constraints = Opening.shared_implied_constraints + PreemptiveBid.shared_implied_constraints
    semantic_bid_class = semanticbids.OpeningPreempt


class PreemptiveOvercall(PreemptiveBid):
    # Jump overcalls are preemptive.
    preconditions = PreemptiveBid.preconditions + [JumpFromLastContract(), UnbidSuit()]
    semantic_bid_class = semanticbids.Preempt


class DirectPreemptiveOvercall(PreemptiveOvercall, DirectOvercall):
    preconditions = DirectOvercall.preconditions + PreemptiveOvercall.preconditions
    shared_implied_constraints = DirectOvercall.shared_implied_constraints + PreemptiveOvercall.shared_implied_constraints


class IndirectPreemptiveOvercall(PreemptiveOvercall, IndirectOvercall):
    preconditions = IndirectOvercall.preconditions + PreemptiveOvercall.preconditions
    shared_implied_constraints = IndirectOvercall.shared_implied_constraints + PreemptiveOvercall.shared_implied_constraints


### Responses to Preempts ###

# FIXME: Add more, better logic for handling preempts.

# Responses to preempts, from p90:
# - Raise is to play (and preemptive)
# - 3NT is to play
# - New suit shows 5+ cards and is forcing for one round (uncapped?)
# -- Opener then:
# -- Raises the new major with 3 card support or doubleton honor.
# -- With a minimum, rebids his own suit
# -- With a maximum, bids a new 4-card suit or NT
# - 2NT is forcing (even if RHO bid).
# -- Opener then:
# -- Rebids suit with a minimum
# -- With maximum: Bids a new suit to show a feature (outside A or protected K/Q)
# -- Lacking a feature, bids 3N with a maximum.


class ResponseToPreempt(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasPreemptive()]


class NewSuitResponseToPreempt(ResponseToPreempt):
    preconditions = ResponseToPreempt.preconditions + [UnbidSuit(), NotJumpFromLastContract()]
    implied_constraints = {
        Rule.ANY_OTHER_BID: [MinLength(5), MinCombinedPointsForPartnerMinimumRebid()],
    }


# FIXME: Need CuebidResponseToPreempt?


class TwoNotrumpFeatureRequest(ResponseToPreempt):
    priority = priorities.TwoNotrumpFeatureRequest
    implied_constraints = {
        # FIXME: These high card points should probably be used for planning, but not for interpretation!
        # This seems to imply at least enough points for opener to rebid at the 3-level with a minimum (17+)?
        '2N': [MinimumCombinedPoints(22)],
    }
    semantic_bid_class = semanticbids.TwoNotrumpFeatureRequest
    explanation = "Shows a strong hand and is looking for an entry in partner's hand (protected king or queen) for a likely NT game.  Bid a new suit at the 3 level to show such an entry, or rebid the preempt suit to deny entries."


class ResponseToTwoNotrumpFeatureRequest(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasTwoNotrumpFeatureRequest()]


class FeatureResponseToTwoNotrumpFeatureRequest(ResponseToTwoNotrumpFeatureRequest):
    preconditions = ResponseToTwoNotrumpFeatureRequest.preconditions + [NotRebidSameSuit()]
    implied_constraints = {
        # The book lists a feature as "an outside ace, or protected king or queen".
        # Anything better than Qxx would be "feature".  That sounds like a 3rd round stopper to me.
        '3C': [MinHonors(HonorConstraint.THIRD_ROUND_STOPPER)],
        '3D': [MinHonors(HonorConstraint.THIRD_ROUND_STOPPER)],
        '3H': [MinHonors(HonorConstraint.THIRD_ROUND_STOPPER)],
        '3S': [MinHonors(HonorConstraint.THIRD_ROUND_STOPPER)],
    }
    # Note: We could have a protected outside honor with as few as 6 points,
    # but unittests would suggest we should count us as having 9+?
    shared_implied_constraints = [MinHighCardPoints(9)]
    priority = priorities.FeatureResponseToTwoNotrumpFeatureRequest


class NotrumpResponseToTwoNotrumpFeatureRequest(ResponseToTwoNotrumpFeatureRequest):
    preconditions = ResponseToTwoNotrumpFeatureRequest.preconditions + [NotRebidSameSuit()]
    implied_constraints = {
        # FIXME: 3N should deny a 3rd round stopper in the other suits?
        # It seems you'd only ever bid 3N, when you have a maximum and all your points are in your suit?
        '3N': [StopperInRHOSuit()],
    }
    shared_implied_constraints = [MinHighCardPoints(9)]
    # FIXME: We wouldn't need priorities if this denied features in all suits!
    priority = priorities.NotrumpResponseToTwoNotrumpFeatureRequest


class MinimumSuitRebidResponseAfterPreempt(Rule):
    preconditions = Rule.preconditions + [MyLastBidWasPreemptive(), NotJumpFromLastContract(), RebidSameSuit(), ForcedToBid()]
    implied_constraints = {
        # The book says this is normally 5-8 hcp in response to a feature request,
        # but a 6-3-2-2 hand with AKQJ (10hcp) in the 6 could have no outside honor, and yet not be rule of twenty.
        # FIXME: We need a way for partner to interpret this response to a feature request as 8hcp, but allow this with more than that.
        Rule.ANY_OTHER_BID: [MaxHighCardPoints(10)],
    }


# class QuickTrickResponseToPreempt(Rule):
#     preconditions = Rule.preconditions + [PartnerWeak(), PartnerHasAtLeastCountInSuit(6), GameOrBelow()]
#
#     def consume_call(self, knowledge, bid):
#         tricks_required_for_contract = bid.level() + 6
#         winners_promised_by_partner = knowledge.partner.min_length(bid.strain) - 1
#         required_tricks = tricks_required_for_contract - winners_promised_by_partner
#         if required_tricks < 0:
#             required_tricks = 0
#         knowledge.me.set_quick_tricks(required_tricks)
#         return knowledge


### Takeout Doubles ###

class TakeoutDouble(Rule):
    # FIXME: Should this be LastBidWasNaturalSuit?  What doubles are takeout against systems like precision (where 1C is artificial)?
    # Do takeout doubles only apply when opponent's opened?
    # FIXME: TakeoutDoubles should not apply if partner has bid, right?
    preconditions = Rule.preconditions + [LastBidWasNaturalSuit(), LastBidWasByOpponents(), LastBidWasBelowGame()]
    priority = priorities.TakeoutDouble
    semantic_bid_class = semanticbids.TakeoutDouble
    shared_implied_constraints = Rule.shared_implied_constraints + [MaximumLengthInOpponentsSuits(2)]
    explanation = "Indicates shortness in the bid suit(s) and asks partner to place the contract."


class TakeoutDoubleToShowUnbidSuits(TakeoutDouble):
    # FIXME: If the opponents have bid 3 suits, I'm not sure what a takeout double means.
    preconditions = TakeoutDouble.preconditions + [MinUnbidSuitCount(2)]
    # Takeout doubles suggest no more than one 3 card suit.
    # The worse possible still-acceptable distribution would be 2-3-4-4
    # with 2 in the opponent's suit.
    shared_implied_constraints = TakeoutDouble.shared_implied_constraints + [SupportForUnbidSuits()]


class OneLevelTakeoutDouble(TakeoutDoubleToShowUnbidSuits):
    preconditions = TakeoutDoubleToShowUnbidSuits.preconditions + [LastBidWasLevel(1)]
    implied_constraints = {
        # p128 says 11+ hcp are needed.  Other places describe it as "an opening hand".
        # Using 12+ points for now.
        # FIXME: This should be dependent on the level of the double.
        # FIXME: This should probably be RuleOf19, 11+hcp or even RuleOf18: 4-4-4-1 and 10hcp?
        'X': [MinHighCardPoints(12), RuleOfTwenty()],
    }


# FIXME: This has nothing to do with the level, only that the opponent's have shown
# a lot of points, thus partner's expected points are smaller.
class TwoLevelTakeoutDouble(TakeoutDoubleToShowUnbidSuits):
    preconditions = TakeoutDoubleToShowUnbidSuits.preconditions + [HaveNotBid(), LastBidWasNotPreemptive()]
    implied_constraints = {
        # Need more points to double if the opponent's have shown real points?
        # We could also just have better shape (singleton or void).
        'X': [MinHighCardPoints(15)],
    }


class TakeoutDoubleAfterPreempt(TakeoutDoubleToShowUnbidSuits):
    preconditions = TakeoutDoubleToShowUnbidSuits.preconditions + [LastBidWasPreemptive(), HaveNotBid()]
    implied_constraints = {
        # FIXME: Don't need any more points to double at higher levels, but we should have better shape?
        'X': [MinHighCardPoints(12), RuleOfTwenty()],
    }


class GenericTakeoutDouble(TakeoutDouble, Rule):
    priority = priorities.InvalidBid
    implied_constraints = {
        # We don't understand the bid, only that it's takeout.
        # We don't even understand what suits it implies, only that it implies shortness in the opponent's suits.
        'X': [MaxLengthForAnySuit(6)],  # With a 7 card suit, you just keep bidding it.
    }
    explanation = "The autobidder doesn't understand this exact bid, but knows its for takeout."


class BalancingTakeoutDouble(TakeoutDoubleToShowUnbidSuits, BalancingOvercall):
    # Balancing doubles only occur after LHO opens and partner and RHO pass.
    # Never later in the auction?
    preconditions = BalancingOvercall.preconditions + TakeoutDoubleToShowUnbidSuits.preconditions
    implied_constraints = {
        # FIXME: Shouldn't this be dependent on the level of the double?
        'X': [MinHighCardPoints(9)],
    }
    shared_implied_constraints = BalancingOvercall.shared_implied_constraints + TakeoutDoubleToShowUnbidSuits.shared_implied_constraints


class ReopeningDouble(Rule):
    # FIXME: Should we expand beyond MaxLevel(2)?
    # p138, suggests that opening doubles be made with 1-2 cards in the opponent's suit
    # with a void, generally one has a better bid to make instead.
    preconditions = [IsDouble(), LastBidWasSuit(), BalancingSeat(), Opened(), MaxLevel(2)]
    priority = priorities.TakeoutDouble
    semantic_bid_class = semanticbids.TakeoutDouble

    def consume_call(self, knowledge, bid):
        lho_suit = knowledge.lho.last_call.strain
        for suit in SUITS:
            if suit == lho_suit:
                knowledge.me.set_max_length(suit, 2)
            else:
                knowledge.me.set_min_length(suit, 3)
        # FIXME: There are no point requirements for this bid?
        return knowledge


### Responses to Takeout Double ###


# Response indicates longest suit (excepting opponent's) with 3+ cards support.
# Cheapest level indicates < 10 points.
# NT indicates a stopper in opponent's suit.  1N: 6-10, 2N: 11-12, 3N: 13-16
# Jump bid indicates 10-12 points (normal invitational values)
# cue-bid in opponent's suit is a 13+ michaels-like bid.
class ResponseToTakeoutDouble(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasTakeoutDouble(), RHOPassed()]


class NotrumpResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = ResponseToTakeoutDouble.preconditions + [IsNotrump(), MaxLevel(3)]
    implied_constraints = {
        '1N': [HighCardPointRange(6, 10)],
        '2N': [HighCardPointRange(11, 12)],
        '3N': [HighCardPointRange(13, 16)],
    }
    shared_implied_constraints = ResponseToTakeoutDouble.shared_implied_constraints + [Balanced(), StoppersInOpponentsSuits()]


class SuitResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = ResponseToTakeoutDouble.preconditions + [IsSuit(), NotSameSuitAsLastContract(), NotJumpFromLastContract()]
    implied_constraints = {
        # FIXME: p125 implies that a non-jump suit bid implies < 9 points.
        # However there are hands with 13 points w/o stoppers in opponent's suit
        # which are too big to jump with and not fit for NT.  For now this
        # it their only option.
        Rule.ANY_OTHER_BID: [LongestSuitExceptOpponentSuits()]
    }


class JumpSuitResponseToTakeoutDouble(ResponseToTakeoutDouble):
    # FIXME: Maybe this is JumpFromLHOLastBid instead of JumpFromLastContract?
    preconditions = ResponseToTakeoutDouble.preconditions + [IsSuit(), NotSameSuitAsLastContract(), JumpFromLastContract(exact_size=1)]
    implied_constraints = {
        # FIXME: This range is wrong when replying to Reoppening Doubles
        Rule.ANY_OTHER_BID: [LongestSuitExceptOpponentSuits(), HighCardPointRange(10, 12)]
    }


class CuebidResponseToTakeoutDouble(ResponseToTakeoutDouble):
    preconditions = ResponseToTakeoutDouble.preconditions + [IsSuit(), SameSuitAsLastContract(), NotJumpFromLastContract()]
    priority = priorities.CueBidAfterTakeoutDouble

    def consume_call(self, knowledge, bid):
        # FIXME: opponent_suit is wrong for two-suited takeout doubles.
        opponent_contract = knowledge.last_contract()
        opponent_suit = opponent_contract.strain
        assert opponent_suit in SUITS

        # Cuebids show 13+ hcp and 4+ cards in available majors.
        knowledge.me.set_min_hcp(13)
        for suit in MAJORS:
            if suit != opponent_suit:
                knowledge.me.set_min_length(suit, 4)
        return knowledge


### Rebids after Takeout Double ###


class RebidAfterTakeoutDouble(Rule):
    preconditions = Rule.preconditions + [MyLastBidWasTakeoutDouble()]


class PassAfterTakeoutDouble(RebidAfterTakeoutDouble):
    priority = priorities.Pass
    preconditions = RebidAfterTakeoutDouble.preconditions + [RHOPassed()]
    implied_constraints = {
        'P': [MaxHighCardPoints(17)],
    }


class RaiseAfterTakeoutDouble(RebidAfterTakeoutDouble):
    # Should this only apply if RHO passed? Otherwise a raise could be competative?
    preconditions = RebidAfterTakeoutDouble.preconditions + [RHOPassed(), RaiseOfPartnersLastSuit(), NotJumpFromLastContract()]
    implied_constraints = {
        # FIXME: Really we just want to remove the constraints added by the double.
        Rule.ANY_OTHER_BID: [ForgetEverythingAboutMe(), MinLength(4), HighCardPointRange(17, 18)],
    }


class JumpRaiseAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = RebidAfterTakeoutDouble.preconditions + [RaiseOfPartnersLastSuit(), JumpFromPartnerLastBid(exact_size=1)]
    implied_constraints = {
        # FIXME: Really we just want to remove the constraints added by the double.
        Rule.ANY_OTHER_BID: [ForgetEverythingAboutMe(), MinLength(4), HighCardPointRange(19, 21)],
    }


class NewSuitAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = RebidAfterTakeoutDouble.preconditions + [UnbidSuit(), NotJumpFromLastContract()]
    implied_constraints = {
        # FIXME: Really we just want to remove the constraints added by the double.
        Rule.ANY_OTHER_BID: [ForgetEverythingAboutMe(), MinLength(5), HighCardPointRange(17, 20)],
    }
    # FIXME: This should be preferred over raising partner's suit when this is a Major and partner's suit is a minor.
    # Board: 4-5d99c5762eac03b376ccaf1842 is an example where this comes up.


class JumpNewSuitAfterTakeoutDouble(RebidAfterTakeoutDouble):
    # FIXME: This uses NewSuit, which currently fails to recognize minors as new suits after the TakeoutDouble.
    preconditions = RebidAfterTakeoutDouble.preconditions + [UnbidSuit(), JumpFromLastContract(exact_size=1)]
    implied_constraints = {
        # FIXME: Really we just want to remove the constraints added by the double.
        # The book describes a jump bid as having a "strong hand", we're interpreting
        # that to mean 21+ points so as not to overlap with a non-jump new suit.
        # If you don't have a self-sustaining suit, a cue-bid (showing 21+) is probably better?
        Rule.ANY_OTHER_BID: [ForgetEverythingAboutMe(), MinLength(6), MinHonors(HonorConstraint.TWO_OF_TOP_THREE), MinHighCardPoints(21)],
    }


class NotrumpAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = RebidAfterTakeoutDouble.preconditions + [IsNotrump(), MaxLevel(3)]
    implied_constraints = {
        '1N': [ForgetEverythingAboutMe(), HighCardPointRange(18, 19)],
        # 2N depends on whether it is a jump.
        '3N': [MinHighCardPoints(22)],  # FIXME: Techincally means 9+ tricks.
    }
    # FIXME: I believe these should imply balanced.
    shared_implied_constraints = [StoppersInOpponentsSuits()]


class NonJumpTwoNotrumpAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = RebidAfterTakeoutDouble.preconditions + [IsNotrump(), Level(2), NotJumpFromLastContract()]
    implied_constraints = {
        # FIXME: I believe this should imply balanced.
        '2N': [ForgetEverythingAboutMe(), HighCardPointRange(19, 20), StoppersInOpponentsSuits()],
    }


class JumpTwoNotrumpAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = RebidAfterTakeoutDouble.preconditions + [IsNotrump(), Level(2), JumpFromLastContract()]
    implied_constraints = {
        # FIXME: I believe this should imply balanced.
        '2N': [ForgetEverythingAboutMe(), HighCardPointRange(21, 22), StoppersInOpponentsSuits()],
    }


class CueBidAfterTakeoutDouble(RebidAfterTakeoutDouble):
    preconditions = RebidAfterTakeoutDouble.preconditions + [NotJumpFromLastContract(), CuebidOfRHOsSuit()]
    implied_constraints = {
        # FIXME: What should this say about shape?
        Rule.ANY_OTHER_BID: [ForgetEverythingAboutMe(), MinHighCardPoints(21)],
    }


class TakeoutDoubleAfterTakeoutDouble(TakeoutDoubleToShowUnbidSuits, RebidAfterTakeoutDouble):
    preconditions = RebidAfterTakeoutDouble.preconditions + TakeoutDoubleToShowUnbidSuits.preconditions
    implied_constraints = {
        'X': [ForgetEverythingAboutMe(), MinHighCardPoints(17)],
    }
    shared_implied_constraints = TakeoutDoubleToShowUnbidSuits.shared_implied_constraints


### More Doubles ###


class LeadDirectingDouble(Rule):
    preconditions = Rule.preconditions + [LastBidWasSuit(), RHOBidWasArtificial()]
    priority = priorities.InvalidBid
    implied_constraints = {
        'X': [],
    }
    semantic_bid_class = semanticbids.LeadDirectingDouble


# FIXME: Refactor this rule to be more declarative.
class NegativeDouble(ResponseToOneLevelSuitedOpen):
    preconditions = ResponseToOneLevelSuitedOpen.preconditions + [
        IsDouble(),
        RHOBidContract(),
        LastBidWasSuit(),
        MaxLevel(2),
    ]
    priority = priorities.NegativeDouble
    semantic_bid_class = semanticbids.NegativeDouble

    # Precondition: knowledge.partner.last_call and knowledge.rho.last_call
    # Indicates 4+ card support in the unbid major. (exactly 4 if that major is spades)
    # 6+ points at the one level, 8/9+ at the two level, 10+ at the 3 level or above.

    def consume_call(self, knowledge, bid):
        partner_suit = knowledge.partner.last_call.strain
        rho_suit = knowledge.rho.last_call.strain
        rho_level = knowledge.rho.last_call.level()

        for suit in MAJORS:
            # Does 1D 2C X really show both majors?  p130 h8 h9 seems to imply so.
            if suit != partner_suit and suit != rho_suit:
                knowledge.me.set_min_length(suit, 4)
            if suit > rho_suit and rho_level == 1 and rho_suit != DIAMONDS:
                # With 5 in the major, we bid it directly unless the bidding
                # is 1C 1D X, in which case we could have 4+/4+ in the majors.
                knowledge.me.set_max_length(suit, 4)

        for suit in MINORS:
            if suit != partner_suit and suit != rho_suit:
                # FIXME: p129 says this is not necessarily true.  We could have support for partner's minor instead of the unbid minor.
                knowledge.me.set_min_length(suit, 3)

        if partner_suit in MAJORS:
            knowledge.me.set_max_length(partner_suit, 2)

        if rho_level == 1:
            knowledge.me.set_min_hcp(6)
        elif rho_level == 2:
            knowledge.me.set_min_hcp(8)
        elif rho_level >= 3:
            # SAYC doesn't play negative doubles above 2S, but we include this
            # rule for completeness.
            knowledge.me.set_min_hcp(10)

        return knowledge


class CueBidAfterNegativedDouble(Rule):
    preconditions = Rule.preconditions + [MyLastBidWasNegativeDouble(), MaxLevel(3), NotJumpFromLastContract(), CuebidOfRHOsSuit()]
    priority = priorities.CueBidAfterNegativedDouble
    implied_constraints = {
        Rule.ANY_OTHER_BID: [MaxLength(1), MinHighCardPoints(12)],
    }
