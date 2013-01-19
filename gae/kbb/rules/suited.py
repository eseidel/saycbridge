from kbb.bidding_priorities import priorities
from kbb.constraints import *
from kbb.handconstraints import HonorConstraint, HandConstraints
from kbb.knowledge import point_systems
from kbb.preconditions import *
from kbb.rules.base import *
from kbb import semanticbids


import logging
_log = logging.getLogger(__name__)


### Shared Concepts ###


class Reverse(object):
    # Andrew says the key to the reverse is that your partner has already denied 4 of that suit?
    # The book states that Reverses exist only at the 2 level.
    # It's unclear what an auction like 1C P 1S 2H P 3D would mean point-wise.
    # Reverses are just another "help suit game try" if we have a fit established.
    preconditions = [SuitHigherThanMyLastSuit(), NotJumpFromLastContract(), Level(2), UnbidSuit(), NoFitEstablished()]


class JumpShift(object):
    # FIXME: Is JumpFromLastContract correct under competition?
    preconditions = [UnbidSuit(), JumpFromLastContract(exact_size=1), BelowGame()]


### Suited Openings ###


class RuleOfTwentyOpening(Opening):
    shared_implied_constraints = Opening.shared_implied_constraints + [RuleOfTwenty(), HighCardPointRange(12, 21)]


class RuleOfFifteenOpening(Opening):
    preconditions = Opening.preconditions + [FourthSeat()]
    shared_implied_constraints = Opening.shared_implied_constraints + [RuleOfFifteen(), HighCardPointRange(10, 21)]


class OneOfAMinor(object):
    implied_constraints = {
        # Do these imply no 5-card major?  No, you could be 5-5 and reversing.
        # 1C implies clubs >= diamonds, 1D implies diamonds >= clubs.
        '1C': [MinLength(3), LongerMinor()], # 1C can be 3-2-4-4, so it's not LongestSuit().
        '1D': [MinLength(3), LongerMinor()], # 1D can be 2-3-4-4, so it's not LongestSuit().
    }

    def priority_for_bid(self, hand, bid):
        suit = bid.strain
        if hand.length_of_suit(suit) > hand.length_of_suit(other_minor(suit)):
            return priorities.LongestMinor
        # Pretend Diamonds are "longest minor" when minors are 4-4 or 5-5.
        if hand.length_of_suit(suit) == hand.length_of_suit(other_minor(suit)):
            if hand.length_of_suit(suit) >= 4 and suit == DIAMONDS:
                return priorities.LongestMinor
        if suit == DIAMONDS:
            return priorities.HigherMinor
        return priorities.LowerMinor

    explanation = "Likely has no 5-card major."


class OneOfAMajor(object):
    implied_constraints = {
        # 1H implies hearts >= spades, 1S implies spades >= hearts.
        '1H': [MinLength(5), LongerMajor()],  # 1H can be 8-0-5-0, not necessarily LongestSuit().
        '1S': [MinLength(5), LongerMajor()],  # 1S can be 8-0-0-5, not necessarily LongestSuit().
    }

    def priority_for_bid(self, hand, bid):
        suit = bid.strain
        if hand.length_of_suit(suit) > hand.length_of_suit(other_major(suit)):
            return priorities.LongestMajor
        if suit == SPADES:
            return priorities.HigherMajor
        return priorities.LowerMajor


class MinorOpen(OneOfAMinor, RuleOfTwentyOpening):
    pass


class MajorOpen(OneOfAMajor, RuleOfTwentyOpening):
    pass


class FourthSeatMinorOpen(OneOfAMinor, RuleOfFifteenOpening):
    pass


class FourthSeatMajorOpen(OneOfAMajor, RuleOfFifteenOpening):
    pass


### Responses to Suited Openings ###


class PassResponseToOneLevelSuitedOpen(ResponseToOneLevelSuitedOpen):
    preconditions = ResponseToOneLevelSuitedOpen.preconditions + [RHOPassed()]
    priority = priorities.Pass
    implied_constraints = {
        # With six or more points, responder always has a bid.
        'P': [HighCardPointRange(0, 5)]
    }


class CheapestNotrumpByResponder(Rule):
    preconditions = Rule.preconditions + [PartnerOpened(), PartnerLastBidWasNaturalSuit()]
    point_system = point_systems.NotrumpSupport
    priority = priorities.NotrumpWithoutStoppers
    implied_constraints = {
        '1N': [HighCardPointRange(6, 10), NoMajorFit(), NoAvailableFourCardSuit()]
    }


class ResponseToMajorOpen(ResponseToOneLevelSuitedOpen):
    preconditions = ResponseToOneLevelSuitedOpen.preconditions + [PartnerLastBidWasNaturalMajor()]


class ResponseToMinorOpen(ResponseToOneLevelSuitedOpen):
    preconditions = ResponseToOneLevelSuitedOpen.preconditions + [PartnerLastBidWasNaturalMinor()]


class NotrumpJumpOverMinor(ResponseToMinorOpen):  # p50
    preconditions = ResponseToMinorOpen.preconditions + [JumpFromLastContract()]
    priority = priorities.NotrumpJumpOverMinor
    implied_constraints = {
        '2N': [HighCardPointRange(13, 15)],
        # Matches SAYC booklet, not the normal book, which has a 17 point cap.
        # The 17 point cap, however, introduces a gap after 1C with 3-3-3-4 and 18 HCP.
        '3N': [HighCardPointRange(16, 18)],
    }

    shared_implied_constraints = ResponseToMinorOpen.shared_implied_constraints + [Balanced(), MaxLength(3, HEARTS), MaxLength(3, SPADES)]


class JordanResponseToMinor(ResponseToMinorOpen):
    preconditions = ResponseToMinorOpen.preconditions + [RHODoubled()]
    point_system = point_systems.SupportPointsIfFit
    implied_constraints = {
        '2N': [SupportForPartnerLastBid(5), MinHighCardPoints(10), NoAvailableFourCardMajor()],
    }


class RaiseResponseToMajorOpen(ResponseToMajorOpen):
    # FIXME: How do these change under competition?
    # I suspect that the 2 level means 8+ hcp when a free bid?
    preconditions = ResponseToMajorOpen.preconditions + [RaiseOfPartnersLastSuit()]
    point_system = point_systems.SupportPointsIfFit
    priority = priorities.RaiseResponseToMajorOpen


class RaiseResponseToMinorOpen(ResponseToMinorOpen):
    # FIXME: How do these change under competition?
    # I suspect that the 2 level means 8+ hcp when a free bid?
    preconditions = ResponseToMinorOpen.preconditions + [RaiseOfPartnersLastSuit()]
    point_system = point_systems.SupportPointsIfFit
    priority = priorities.RaiseResponseToMinorOpen


class MinimumRaise(object):
    # FIXME: Unclear how this changes when RHO bids?
    # When RHO doubles, this is the same (p122).
    preconditions = [Level(2)]

    # Partner can have 12-21 points.
    # (Ro20 will open 11hcp (5-4) or 10hcp (5-5), but with length points for the 5-card suits is at least 12).
    # We could miss game if we passed with 5 points,
    # but 12 + 5 == 17 is rather light for the 2 level (19 points should make comfortably).
    # It seems the system compromises to miss 20 + 5 games and avoid 12 + 5 disasters.
    implied_constraints = {
        # This is shaded down 1 point from SuitedToPlay, which would be 7-9.
        Rule.ANY_OTHER_BID: [MinimumCombinedLength(8), HighCardPointRange(6, 9)],
    }

class MinimumRaiseResponseToMajorOpen(MinimumRaise, RaiseResponseToMajorOpen):
    preconditions = RaiseResponseToMajorOpen.preconditions + MinimumRaise.preconditions


class MinimumRaiseResponseToMinorOpen(MinimumRaise, RaiseResponseToMinorOpen):
    preconditions = RaiseResponseToMinorOpen.preconditions + MinimumRaise.preconditions


class JumpRaiseResponseToMajorOpen(RaiseResponseToMajorOpen):
    # FIXME: Unclear how these are changed when RHO bids.
    # When RHO doubles, this becomes preemptive and Jordan 2NT is used for invitational values.
    preconditions = RaiseResponseToMajorOpen.preconditions + [Level(3), RHODidNotDouble()]
    # Likewise, if we count partner at a minimum of 12, then we're 1 trick short with 10 points.
    # min_hcp = 22 - 12 = 10, so we bit one-trick short of game.
    # If we have 13 points, then we know that we have game, but don't bid it directly
    # as that's reserved for the 5-card support game-jump preempt.
    implied_constraints = {
        # This is shaded down 1 point from SuitedToPlay, which would be 10-12.
        Rule.ANY_OTHER_BID: [MinLength(3), HighCardPointRange(10, 11)],
    }


class JumpRaiseResponseToMajorOpenAfterRHOTakeoutDouble(RaiseResponseToMajorOpen):
    preconditions = RaiseResponseToMajorOpen.preconditions + [Level(3), RHODoubled()]
    implied_constraints = {
        Rule.ANY_OTHER_BID: [MinLength(4), MaxHighCardPoints(9)],
    }
    priority = priorities.JumpRaiseResponseToMajorOpenAfterRHOTakeoutDouble


class JumpRaiseResponseToMinorOpenAfterRHOTakeoutDouble(RaiseResponseToMinorOpen):
    preconditions = RaiseResponseToMinorOpen.preconditions + [Level(3), RHODoubled()]
    implied_constraints = {
        # FIXME: The book talks about 4-card support for jump-raises, but I expect it means
        # 5-card support for minors.
        # FIXME: 2D should only imply 4-diamonds, but because 1D currently only shows 4
        # this bid will overlap with 2D in both showing 5+.
        Rule.ANY_OTHER_BID: [MinLength(5), MaxHighCardPoints(9)],
    }
    priority = priorities.JumpRaiseResponseToMinorOpenAfterRHOTakeoutDouble


class JordanResponseToMajor(ResponseToMajorOpen):
    preconditions = ResponseToMajorOpen.preconditions + [RHODoubled()]
    point_system = point_systems.SupportPointsIfFit
    implied_constraints = {
        '2N': [SupportForPartnerLastBid(3), MinHighCardPoints(10)],
    }
    semantic_bid_class = semanticbids.Jordan


class RedoubleResponseToMajorAfterRHOTakeoutDouble(ResponseToMajorOpen):
    preconditions = ResponseToMajorOpen.preconditions + [RHODoubled()]
    implied_constraints = {
        # Definitely no 6-card suit.  Unclear what else this shows.
        'XX': [MaximumLengthInLastBidSuit(2), MinHighCardPoints(10)],
    }


class GameJumpRaiseResponseToMajorOpen(RaiseResponseToMajorOpen):
    preconditions = RaiseResponseToMajorOpen.preconditions + [Level(4)]
    priority = priorities.GameJumpRaiseResponseToMajorOpen
    # 5-3-3-2 hands with 11/12 support points (10/11 hcp and 5 trump) are too big
    # for this game-jump preempt, but too small for Jacoby2N (not Ro20)
    # so just end up being invitational.
    implied_constraints = {
        Rule.ANY_OTHER_BID: [MinLength(5), MaxHighCardPoints(10)],
    }


# Our first priority is our cheapest-available, highest 5-card suit.
# Second priority is our cheapest-available, lowest-4-card-suit.
# Partner opens 1D, 5c order: 1S (5), 1H (5), 1H (4), 1S (4), 2C (4 or 5)
# Partner opens 1C, 5c order: 1S, 1H, 1D
class NewOneLevelSuitByResponder(ResponseToOneLevelSuitedOpen):
    preconditions = ResponseToOneLevelSuitedOpen.preconditions + [UnbidSuit(), Level(1)]
    # We don't cap at 18, because it's possible to have a 19+ point balance hand
    # and not be able to jump-shift (requires 5+ in the target suit).
    shared_implied_constraints = [MinLength(4), MinHighCardPoints(6)]

    def priority_for_bid(self, hand, bid):
        suit = bid.strain
        if suit in MAJORS:
            suit_length = hand.length_of_suit(suit)
            if suit_length > hand.length_of_suit(other_major(suit)):
                return priorities.LongestNewMajor
            if suit == SPADES:
                return priorities.HigherFourCardMajor if suit_length == 4 else priorities.HigherMajor
            return priorities.LowerFourCardMajor if suit_length == 4 else priorities.LowerMajor
        return priorities.NewSuit


class NewOneLevelSuitByResponderNoCompetition(NewOneLevelSuitByResponder):
    # One-level new suit bids are normal after RHO TakeoutDouble.
    preconditions = NewOneLevelSuitByResponder.preconditions + [RHODidNotBidContract()]
    implied_constraints = {
        '1D': [MaxLength(3, HEARTS), MaxLength(3, SPADES)],
        '1H': [LongerMajor()],
        '1S': [LongerMajor()],
    }


class NewOneLevelSuitByResponderAfterRHOOneDiamonds(NewOneLevelSuitByResponder):
    preconditions = NewOneLevelSuitByResponder.preconditions + [RHOBidContract(), LastBidWas('1D')]
    implied_constraints = {
        '1H': [LongerMajor()],
        '1S': [LongerMajor()],
    }


class NewOneLevelSuitByResponderInCompetition(NewOneLevelSuitByResponder):
    preconditions = NewOneLevelSuitByResponder.preconditions + [RHOBidContract()]
    implied_constraints = {
        '1S': [MinLength(5)],
    }


# Responses after RHO makes a Takeout Double (p121-122)
# - Redouble shows 10+hcp and (generally) denies fit
# - Limit raise over the double is normal.
# - Jump raise is preemptive, showing 4 card support (and few points?)
# - Jump raise to game is preemptive like normal.
# - 2NT shows limit raise in opener's suit (Jordan), over a minor 5+ card support and 10+ hcp
# - 1 level new suit is normal
# - 2 level new suit shows 5 and "invitational" points?
# - Jump-shift is preemptive.


# For responses which apply to either openings or overcalls.
class SuitResponse(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasNaturalSuit(), PartnerLastBidWasNotPreemptive()]


class NewTwoLevelSuitByResponder(SuitResponse):
    preconditions = SuitResponse.preconditions + [UnbidSuit(), NotJumpFromLastContract()]
    priority = priorities.NewSuit
    implied_constraints = {
        # LessThanFourCardsInAllSkippedSuits is equivalent to NoAvailableFourCardMajor for clubs.
        # FIXME: We may need a way to make this 2C bid with only 3 clubs when we have nothing better to say.
        # Example: http://www.saycbridge.com/bidder/10-ca4d11e0a301f6ebe2e7792355:1S,P,P,P
        '2C': [MinLength(4), LessThanFourCardsInAllSkippedSuits()],
        # LessThanFourCardsInAllSkippedSuits implies that we don't have 4 clubs or 4 of a major (if they were available).
        '2D': [MinLength(4), LessThanFourCardsInAllSkippedSuits()],
        '2H': [MinLength(5)],
        '2S': [MinLength(5)],
    }
    shared_implied_constraints = [HighCardPointRange(10, 18)]


# This only occurs over 2-level preempts.
# If we had two places to play, we would use a negative double.
class NewThreeLevelSuitByResponder(OpeningResponse):
    preconditions = OpeningResponse.preconditions + [UnbidSuit(), NotJumpFromLastContract()]
    priority = priorities.NewSuit
    implied_constraints = {
        # FIXME: Should this deny 5 cards in other suits besides partner's?
        Rule.LEVEL_3: [],
    }
    # Mentioning a new suit at the 3 level is going to land us in game, so better have the points for it.
    # FIXME: Should this deny a fit?
    shared_implied_constraints = [MinLength(5), MinimumCombinedPoints(25)]


class JumpShiftResponseToOpen(ResponseToOneLevelSuitedOpen):
    preconditions = ResponseToOneLevelSuitedOpen.preconditions + JumpShift.preconditions
    priority = priorities.JumpShift
    implied_constraints = {
        # Unclear why the book says this is 19 hcp.  Seems it should be smaller for Responder.
        # According to p43 and p50 a jump-shift by responder shows a 5-card suit. 
        Rule.ANY_OTHER_BID: [MinHighCardPoints(19), MinLength(5)],
    }


class JumpShiftResponseToOpenAfterRHODouble(ResponseToOneLevelSuitedOpen):
    preconditions = ResponseToOneLevelSuitedOpen.preconditions + JumpShift.preconditions + [RHODoubled()]
    # FIXME: Unclear what priority bid this should have.
    implied_constraints = {
        # JumpShifts after RHO's TakeoutDouble are preemptive.
        # Unclear if this should be 2o3 or 3o5.  Starting with 2o3.
        Rule.ANY_OTHER_BID: [HighCardPointRange(5, 10), MinLength(6), MinHonors(HonorConstraint.TWO_OF_TOP_THREE), NoFit()],
    }


### Rebids by Opener ###


class CheapestNotrumpByOpener(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [PartnerBid()]
    implied_constraints = {
        # The book says the maximum point value here is 14, but there are some
        # 15 point hands that are too weak to reverse and have no other bid.
        # e.g., K67.AKT92.J975.A
        # This bid almost implies balanced, but not quite.  Most unbalanced distributions:
        # 1C-1H-1N: 5-4-3-1, 5-2-3-3, 5-4-1-3
        # 1C-1S-1N: 5-4-4-0 can't bid 2D or 2H as that would be a reverse, also 5-1-4-3.
        # 1D-1H-1N: 4-5-3-2, 3-5-3-2, 4-4-2-3 or 4-4-3-2. Balanced. Always 4+ diamonds.
        # 1D-1S-1N: 3-5-4-1, 2-5-4-2.  Always 4+ diamonds.
        # 1H-1S-1N: 3-2-5-3 or 3-3-5-2.  Balanced.
        # FIXME: We should dynamically compute min lengths based on partners bid.
        # FIXME: These lengths could be wrong under competition?
        # Promising no second 5 card suit.
        '1N': [
            HighCardPointRange(12, 15),
            NoMajorFit(),
            NoAvailableFourCardSuit(),
            NoAvailableNonReverse(),
            MaxLengthForAnySuit(5),
            LongestMinorOrMajorIsNowLongestSuit(),
            NoSecondFiveCardSuit(),  # Depends on being after LongestMinorOrMajorIsNowLongestSuit.
        ]
    }


class NewOneLevelMajorByOpener(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [MyLastBidWasOneOfASuit(), UnbidSuit()]
    priority = priorities.NewSuit

    # FIXME: What is opener supposed to when 5/5 in clubs and spades and opens
    # clubs planning to reverse? When partner responds 1D, can opener rebid 1S
    # with five?
    implied_constraints = {
        "1H": [MaxLength(4, SPADES)],
        "1S": [MaxLength(3, HEARTS)],
    }

    shared_implied_constraints = [MaxHighCardPoints(18), Length(4)]


class NewSuitByOpener(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [MyLastBidWasOneOfASuit(), UnbidSuit(), SuitLowerThanMyLastSuit(), NotJumpFromLastContract()]
    priority = priorities.NewSuit
    implied_constraints = {
        # With >18 hcp, we would have jump-shifted.
        # FIXME: Doesn't this deny support for partner's suit?
        # 1H and 1S are covered by NewOneLevelMajorByOpener.  I don't think 1D is ever possible?

        '2C': [],
        '2D': [],
        '2H': [],  # Should be possible in 1S P 2C P 2H with 5-5 or better in the majors?
        # 2S would necessarily be a reverse, or a jumpshift, and is not coverd by this rule.

        # New suits at the 3 level are a game-force, according to p53, h13.
        # So 15+ hcp?  Maybe this should be MinimumCombinedPoints(25)?
        # Another way to look at it would be to compare it to a reverse (which is normally 16-18hcp)
        # in that it forces your partner to the 3 level if he wants to sign-off in your original suit.
        # FIXME: Should these show 5+?  Seems silly to mention a 4-card suit at the 3-level,
        # especially if partner hasn't said anything.
        '3C': [MinimumCombinedPoints(25)],
        '3D': [MinimumCombinedPoints(25)],
        '3H': [MinimumCombinedPoints(25)],
    }

    shared_implied_constraints = [MaxHighCardPoints(18), MinLength(4), NoMajorFit(), LessThanFourCardsInAllSkippedSuits()]



class RebidOriginalSuitByOpener(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [MyLastBidWasOneOfASuit(), RebidSameSuit(), NotJumpFromLastContract(), MaxLevel(2)]

    def _am_forced_to_bid(self, knowledge, bid):
        assert knowledge.partner.last_call.strain != bid.strain
        if knowledge.rho.last_call.is_contract():
            return False
        if knowledge.last_contract().strain == NOTRUMP:
            return False
        if knowledge.partner.last_call.is_pass():
            return False
        return True

    def _length_shown(self, knowledge, bid):
        can_rebid_with_skipping_notrump = knowledge.last_contract().strain < bid.strain
        if self._am_forced_to_bid(knowledge, bid) and can_rebid_with_skipping_notrump:
            return 5
        return 6

    def consume_call(self, knowledge, bid):
        # We can't skip over four-card majors.
        # FIXME: This should just use NoAvailableFourCardMajor()
        if knowledge.partner.last_call.level() == 1:
            for suit in MAJORS:
                if suit <= knowledge.me.last_call.strain:
                    continue
                if suit != knowledge.partner.last_call.strain:
                    if knowledge.rho.min_length(suit) >= 4 or knowledge.lho.min_length(suit) >= 4:
                        continue  # This major belongs to the opponents.
                    if knowledge.partner.min_length(suit) <= 3:
                        knowledge.me.set_max_length(suit, 4)
                        continue  # Partner skipped this major, thus we'd only bid it if we had 5.
                    knowledge.me.set_max_length(suit, 3)

        # FIXME: In general skipping over any unbid suits denies 4 in them.

        length_shown = self._length_shown(knowledge, bid)
        # When rebidding our suit we deny a fit with partner's major.  If we're only
        # promising 5 in our rebid, than we've denied a fit in his minor too.
        partner_suit = knowledge.partner.last_call.strain
        if partner_suit is not None and (partner_suit in MAJORS or length_shown == 5):
            knowledge.me.set_max_length(partner_suit, 8 - knowledge.partner.min_length(partner_suit) - 1)

        # FIXME: We should split forced vs. non-forced rebid into separate rules.
        knowledge.me.set_max_hcp(15)  # Otherwise we could have JumpRebidOriginalSuitByOpener, jump-shifted, reversed or bid a NT.
        knowledge.me.set_min_length(bid.strain, length_shown)
        # FIXME: We not supposed to do this if we're balanced.
        return knowledge


class RaisePartnersSuit(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [MyLastBidWasOneOfASuit(), NotJumpFromLastContract(), NotRebidSameSuit(), IsSuit(), PartnerHasAtLeastCountInSuit(4), MaxLevel(3)]

    implied_constraints = {
        # Should this imply a maximum point value? With many points, the
        # opener probably need to do something else to show a non-minimum.
        Rule.ANY_OTHER_BID : [MinimumCombinedLength(8), HighCardPointRange(12, 15)]
    }


# JumpRaisePartnersSuit is covered by SuitedToPlay.


class OpenerSuitRebid(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [MyLastBidWasOneOfASuit(), RebidSameSuit()]


class InviteByRaisingSuit(OpenerSuitRebid):
    # FIXME: This should be covered by a more general UnforcedSuitedToPlay.
    preconditions = OpenerSuitRebid.preconditions + [NotJumpFromLastContract(), RaiseOfPartnersLastSuit(), BelowGame()]
    implied_constraints = {
        # FIXME: CombinedPointRangeOverPartnerMinimum is probably wrong here under competition
        # this is a descriptive bid, not a contract placement bid.
        Rule.ANY_OTHER_BID : [MinLength(6), CombinedPointRangeOverPartnerMinimum(22, 24)]
    }


class NotrumpInvitationByOpener(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [MyLastBidWasOneOfASuit(), NotJumpFromLastContract(), FitEstablishedInSomeSuit()]
    implied_constraints = {
        # FIXME: CombinedPointRangeOverPartnerMinimum is probably wrong here under competition
        # this is a descriptive bid, not a contract placement bid.
        # If we're not balanced, than we'd have a HelpSuitGameTry to use instead.
        '2N': [CombinedPointRangeOverPartnerMinimum(22, 24), Balanced()]
    }


class HelpSuitGameTry(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [
        MaxLevel(3), # Should this be BelowGame()?  Is 4C a HelpSuitGameTry over 3D?
        MyLastBidWasOneOfASuit(),
        NotJumpFromLastContract(),  # FIXME: Should this be NotJumpFromPartnerLastBid()?
        FitEstablishedInSomeSuit(),
        UnbidSuit(),
    ]
    implied_constraints = {
        # FIXME: This range should be dependent on the level of the bid, no?
        Rule.ANY_OTHER_BID : [MinLength(4), MinHonors(HonorConstraint.THIRD_ROUND_STOPPER), HighCardPointRange(16, 18)]
    }


class OpenerRebidAfterLimitRaise(OpenerSuitRebid):
    # Partner must have made a limit raise to one short of game.
    # FIXME: Do we need to check LHOPassed()? In that case, the syntax for
    # limit raises are different.
    preconditions = OpenerSuitRebid.preconditions + [RaiseOfPartnersLastSuit(), NotJumpFromLastContract(), IsGame()]
    priority = priorities.OpenerRebidAfterLimitRaise
    implied_constraints = {
        # FIXME: The book recomends:
        #   If hand is NOT balanced and >= 14 hcp, bid game.  Otherwise pass.
        # This heuristic works for some hands, but not all, we need to re-write this as an OR.
        Rule.ANY_OTHER_BID : [CombinedPointRangeOverPartnerMinimum(24, 32)]
    }


# FIXME: This should be renamed to ThreeLevelRebidByOpener?
class JumpRebidOriginalSuitByOpener(OpenerSuitRebid):
    preconditions = OpenerSuitRebid.preconditions + [NotRaiseOfPartnersLastSuit(), JumpFromMyLastBid(exact_size=1), BelowGame()]
    implied_constraints = {
        Rule.ANY_OTHER_BID : [MinLength(6), HighCardPointRange(16, 18)]
    }


# FIXME: This should be renamed to FourLevelRebidByOpener?
class DoubleJumpRebidByOpener(OpenerSuitRebid):
    # FIXME: This is only a jump relative to your own bid.  Doesn't work over competition.
    preconditions = OpenerSuitRebid.preconditions + [NotRaiseOfPartnersLastSuit(), JumpFromMyLastBid(exact_size=2)]
    implied_constraints = {
        Rule.ANY_OTHER_BID : [MinLength(6), HighCardPointRange(19, 21)]
    }
    def priority_for_bid(self, hand, bid):
        is_game = IsGame()._game_level(bid.strain) == bid.level()
        if not is_game:
            return priorities.Default

        if bid.strain in MAJORS:
            return priorities.MajorGame
        return priorities.MinorGame


# DoubleJumpRaiseByOpener is covered by SuitedToPlay.


class OpenerReverse(OpenerRebid):
    preconditions = OpenerRebid.preconditions + Reverse.preconditions + [MyLastBidWasOneOfASuit()]
    priority = priorities.Reverse

    def consume_call(self, knowledge, bid):
        # FIXME: In 2-over-1 auctions (1H P 2C P 2S) a reverse shows only 15+ points.
        # FIXME: The book is unclear about whether this is 16 or 17 points.  The book even has 15 point examples.
        # FIXME: Seems this should be capped at 18 hcp (otherwise we would jump-shift), but the book
        # says reverses are forcing for one round, thus they must be uncapped.
        knowledge.me.set_min_hcp(16)
        knowledge.me.set_min_length(bid.strain, 4)
        # FIXME: We should be able to imply relative length in the first and second suit from the second bid?
        first_suit = knowledge.me.last_call.strain
        if first_suit == CLUBS:
            # Since clubs only promises 3 at the 1 level, a reverse should indicate that intial club bid was 4+ too.
            knowledge.me.set_min_length(first_suit, 4)
        return knowledge


class JumpShiftByOpener(OpenerRebid):
    preconditions = OpenerRebid.preconditions + [MyLastBidWasOneOfASuit()] + JumpShift.preconditions
    priority = priorities.JumpShift
    implied_constraints = {
        # FIXME: The book mentions that you jumpshifts don't always promise 4, especially for 1C P MAJOR P 3D
        Rule.ANY_OTHER_BID : [MinHighCardPoints(19), MinLength(4)],
    }


class DelayedSupportByOpener(Rule):
    preconditions = Rule.preconditions + [
        Opened(),
        IsSuitedProtocol(),
        MyLastBidWasNotOpen(),
        NotRebidSameSuit(),
        NotJumpFromLastContract(),
        PartnerHasAtLeastCountInSuit(4),
        NotSuitWithFit(),
    ]
    implied_constraints = {
        # Since may push the bidding up to the next level, and possibly NT, we should
        # at least have points necessary to bid the next level of NT.
        # Should these ranges be different for free bids vs. forced bids?
        # We may be forcing him to escape to the next level
        # if he doesn't have NT stoppers, and if he only has 4 cards in the
        # suit we're showing delayed support for.
        '2H': [CombinedPointRangeOverPartnerMinimum(22, 29)],
        '2S': [CombinedPointRangeOverPartnerMinimum(22, 29)],
        # FIXME: We may need stoppers in unbid suits here, since partner may be forced to 3N?
        '3H': [CombinedPointRangeOverPartnerMinimum(25, 29)],
        '3S': [CombinedPointRangeOverPartnerMinimum(25, 29)],
    }
    shared_implied_constraints = [MinLength(3)]
    priority = priorities.DelayedSupportByOpener


### Subsequent Bidding by Responder ###


class ResponderRebid(Rule):
    preconditions = Rule.preconditions + [PartnerOpened(), HaveBid(), IsSuitedProtocol()]


class ResponderSuitRebid(ResponderRebid):
    preconditions = ResponderRebid.preconditions + [RebidSameSuit()]


class RebidResponderSuitByResponder(ResponderSuitRebid):
    preconditions = ResponderSuitRebid.preconditions + [MaxLevel(2), NotRaiseOfPartnersLastSuit()]
    implied_constraints = {
        Rule.ANY_OTHER_BID : [MinLength(6), HighCardPointRange(6, 9)],
    }


class ThreeLevelSuitRebidByResponder(ResponderSuitRebid):
    # Shows invitational points, according to page 74.
    preconditions = ResponderSuitRebid.preconditions + [Level(3), NotRaiseOfPartnersLastSuit(), UnsupportedSuit(), MaxShownCount(5)]
    implied_constraints = {
        # FIXME: CombinedPointRangeOverPartnerMinimum is probably wrong here under competition
        # this is a descriptive bid, not a contract placement bid.
        # We might have game points, but without a fit can't bid it.
        Rule.ANY_OTHER_BID : [MinLength(6), CombinedPointRangeOverPartnerMinimum(22, 25)],
    }


# FIXME: I do not understand this rule.
# It gets us into trouble in at least one place:
# http://saycbot.appspot.com/bidder/5-4f5f37aa58112240e1cda993fe:P,P,1S,P,1N,P,2D,P,2H,P,2S,P,P,P
class DelayedNewSuitByResponder(ResponderRebid):
    preconditions = ResponderRebid.preconditions + [MaxLevel(2), IsSuit(), NotRebidSameSuit(), NotRaiseOfPartnersLastSuit()]
    implied_constraints = {
        Rule.ANY_OTHER_BID : [MinLength(6), HighCardPointRange(6, 9)],
    }


class ResponderSignoffInPartnersSuit(ResponderRebid):
    preconditions = ResponderRebid.preconditions + [MaxLevel(2), IsSuit(), NotRaiseOfPartnersLastSuit(), PartnerHasAtLeastCountInSuit(3)]
    implied_constraints = {
        # FIXME: This should prefer to sign off in the major over the minor
        # when both are available, such as board 6-6de0ed5387202cf8997970a739
        # FIXME: Should this deny having a 6-card suit?  Otherwise we would rebid our suit
        # as in board 5-ffc3835881b64ba987b6d05760.
        # FIXME: This should use some sort of maximum combined point instead of HighCardPointRange.
        # If partner has already limited himself such as with "P,P,1D,P,1S,P,1N,P" from 6-1cc61a8fe185d429cece79639c
        # than we can have more than 9 points here.
        Rule.ANY_OTHER_BID : [MinimumCombinedLength(7), HighCardPointRange(6, 9)],
    }


class ResponderSignoffInMinorGame(ResponderRebid):
    preconditions = ResponderRebid.preconditions + [IsGame(), IsSuit(), PartnerHasAtLeastCountInSuit(3), NotRebidSameSuit()]
    point_system = point_systems.SupportPointsIfFit
    priority = priorities.MinorGame

    implied_constraints = {
        # Responder can sign-off in a minor game with slightly fewer points than usual.
        '5C': [CombinedPointRangeOverPartnerMinimum(25, 30)],
        '5D': [CombinedPointRangeOverPartnerMinimum(25, 30)],
    }

    shared_implied_constraints = [MinimumCombinedLength(8), NoMajorFit()]


class ResponderReverse(ResponderRebid):
    preconditions = ResponderRebid.preconditions + Reverse.preconditions
    priority = priorities.Reverse
    implied_constraints = {
        # Reverses by responder show an opening hand or better (p65).
        # 19+ points and he would jump-shift instead.
        # FIXME: We should be able to imply relative length in the first and second suit from the second bid?
        Rule.ANY_OTHER_BID : [HighCardPointRange(12, 18), MinLength(4)],
    }


class JumpShiftResponderRebid(ResponderRebid):
    # FIXME: JumpShifts don't exist in NotrumpAuctions.
    # Need some sort of knowledge.notrump_auction()?
    preconditions = ResponderRebid.preconditions + JumpShift.preconditions
    implied_constraints = {
        # p71 and p74 state that a "second round" jump shift is "usually" a game force.
        # Unclear what point values that would mean.  For now using 14,
        # since the initial 1-level suit (per h14, p71) indicated < 18 hcp.
        # JumpShifts as a ResponderRebid are covered by h14 and p71.
        # It shows a 5-5-3-0 hand, but I would expect it to be possible with 5-4-3-1 too.
        # Hence showing only 4+ in the second suit.
        Rule.ANY_OTHER_BID : [MinHighCardPoints(14), MinLength(4)],
    }


### 2C Auctions ###


class StrongTwoClubs(Opening):
    # FIXME: This could also imply 9+ quick tricks.
    implied_constraints = {
        '2C': [MinHighCardPoints(22)],
    }
    priority = priorities.StrongTwoClubs
    semantic_bid_class = semanticbids.StrongTwoClubs


class ResponseToStrongTwoClubs(OpeningResponse):
    preconditions = OpeningResponse.preconditions + [PartnerLastBidWas('2C'), PartnerMinimumHighCardPoints(22)]


class WaitingResponseToStrongTwoClubs(ResponseToStrongTwoClubs):
    priority = priorities.NegativeResponseOppositeTwoClubs
    implied_constraints = {
        '2D': [MaxHighCardPoints(7)],  # Nothing better to say.
    }
    semantic_bid_class = semanticbids.Artificial


class SuitResponseToStrongTwoClubs(ResponseToStrongTwoClubs):
    point_system = point_systems.LengthPoints
    priority = priorities.GoodSuitOppositeTwoClubOpen
    implied_constraints = {
        # FIXME: What order should two good 5 card suits be bid in?  Major first?
        '2H': [],
        '2S': [],
        '3C': [],
        '3D': [],
    }
    shared_implied_constraints = [MinLength(5), MinHonors(HonorConstraint.TWO_OF_TOP_THREE), MinHighCardPoints(8)]


class NotrumpResponseToStrongTwoClubs(ResponseToStrongTwoClubs):
    priority = priorities.NoBidableSuitOppositeTwoClubOpen
    implied_constraints = {
        '2N': [MinHighCardPoints(8)],  # No bidable suit, but 8+ points.
    }


class OpenerRebidAfterStrongTwoClubs(OpenerRebid):
    # FIXME: Another way do to this would be to make strong_two_club a flag on SemanticBid.
    preconditions = OpenerRebid.preconditions + [MyLastBidWas('2C'), MinimumHighCardPoints(22)]


class OpenerSuitedRebidAfterStrongTwoClubs(OpenerRebidAfterStrongTwoClubs):
    preconditions = OpenerRebidAfterStrongTwoClubs.preconditions + [UnbidSuit(), NotJumpFromLastContract(), MaxLevel(4)]
    # Suit bids are natural.  Majors are forcing to the 3 level, Minors to the 4 level.
    # Presumably either promises at least 5 cards (since otherwise we'd bid another suit or NT, no?)
    implied_constraints = {
        Rule.ANY_OTHER_BID: [MinLength(5), NoMajorFit()],
    }


class OpenerSuitedJumpRebidAfterStrongTwoClubs(OpenerRebidAfterStrongTwoClubs):
    preconditions = OpenerRebidAfterStrongTwoClubs.preconditions + [UnbidSuit(), JumpFromLastContract(exact_size=1)]
    # A Jump-Rebid in a suit is game-forcing and shows a self-supporting holding (6? 7? 2o3?)
    implied_constraints = {
        # FIXME: Should this deny a major fit?
        # Interpreting "self-supporting" to mean 7, even though 6 might make more sense.
        # We should be comfortable playing with 7 trumps even if partner has 0.
        Rule.ANY_OTHER_BID: [MinLength(7)],
    }
    shared_implied_constraints = [MinHonors(HonorConstraint.TWO_OF_TOP_THREE)]


# FIXME: We should add an OpenerRebid of 3N over 2C P 2N P to show a minimum 22-24 HCP
# instead of jumping to 5N which just wastes bidding space.
# This is not covered in the book or the SAYC pdf.


class SecondNegative(ResponderRebid):
    # If history goes: 2C,2D,2N, then this doesn't apply.
    preconditions = ResponderRebid.preconditions + [NotJumpFromLastContract(), PartnerMinimumHighCardPoints(22), PartnerLastBidWasNaturalSuit(), MyLastBidWas('2D')]
    implied_constraints = {
        '3C': [NoFit(), MaxHighCardPoints(3)]
    }
    semantic_bid_class = semanticbids.Artificial
