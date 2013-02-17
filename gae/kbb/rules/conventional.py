from kbb.bidding_priorities import priorities
from kbb.constraints import *
from kbb.handconstraints import HonorConstraint, HandConstraints, ControlConstraint
from kbb.knowledge import point_systems
from kbb.preconditions import *
from kbb.rules.base import *
from kbb.rules.suited import ResponseToMajorOpen
from kbb import semanticbids


import logging
_log = logging.getLogger(__name__)


class Jacoby2N(ResponseToMajorOpen):
    preconditions = ResponseToMajorOpen.preconditions + [RHOPassed()]
    implied_constraints = {
        # 2N is unbounded.
        # Note: The book says Jacoby2N promises 4, but that leaves a point
        # gap for game-forcing hands with no biddable 4-card suit and 13-18 points.
        # For example, after 1S P, holding 3-3-4-3, Jacoby2N makes the most sense.
        # Jacoby2N is basically highest priority if you have 4-card support, but
        # temporizing with a new suit is better if you only have 3 card support.
        # The book says high card points, but we're using 14 LengthPoints instead
        # to allow bidding Jacoby with a 12hcp hand and 5 card support.
        '2N': [SupportForPartnerLastBid(4), MinHighCardPoints(14)]
    }
    point_system = point_systems.LengthPoints
    priority = priorities.Jacoby2N
    semantic_bid_class = semanticbids.Jacoby2N


class ResponseToJacoby2N(Rule):
    # Bids above 4NT are either natural or covered by other conventions.
    preconditions = Rule.preconditions + [PartnerLastBidWasJacoby2N()]
    # FIXME: Most of these responses should be marked as artificial!

    def consume_call(self, knowledge, bid):
        if not bid.is_contract() or bid.level() > 4 or bid.name == '4N':
            # Jacoby 2N is a game-force, and you have a sub-game bid for when
            # you're strong.  Anything 4N or above is nonsense.
            return None

        trump_suit = knowledge.me.last_call.strain
        if bid.strain not in (trump_suit, NOTRUMP):
            if bid.level() == 3:
                knowledge.me.set_max_length(bid.strain, 1)
            else:
                knowledge.me.set_min_length(bid.strain, 5)
                knowledge.me.set_min_honors(bid.strain, HonorConstraint.THREE_OF_TOP_FIVE)
            return knowledge

        # Singleton and side 6-card suits are highest priority, so
        # bidding anything else is denying both.
        for suit in SUITS:
            if suit == trump_suit:
                continue
            knowledge.me.set_length_range(suit, 2, 5)

        if bid.strain == trump_suit:
            if bid.level() == 3:
                knowledge.me.set_min_hcp(18)
            else:
                # Direct game-jump is a minimum opener.
                knowledge.me.set_max_hcp(14)
            return knowledge

        assert bid.name == '3N'
        knowledge.me.set_hcp_range(15, 17)
        return knowledge


class FourthSuitForcing(Rule):
    # Bid of the only unbid suit at the two level or higher.
    # Unclear if it includes suits bid by opponents.
    preconditions = [MinLevel(2), OnlyPartnershipUnbidSuit(), NotJumpFromLastContract()]
    semantic_bid_class = semanticbids.FourthSuitForcing
    priority = priorities.InvalidBid  # We do not yet know how to plan FSF.
    implied_constraints = {
        # Definitely denies a stopper in the suit, probably fewer than 3 cards length.
        # MinCombinedPointsForPartnerMinimumRebid means that we've shown enough points for partner to rebid cheapest NT safely.
        Rule.ANY_OTHER_BID: [MaxLength(3), MinCombinedPointsForPartnerMinimumRebid()]
    }


# FIXME: 1C P 1D P 1H P 2S* is a special FSF because it's a jump.
class TwoSpadesJumpFourthSuitForcing(Rule):
    preconditions = [OnlyPartnershipUnbidSuit()]
    semantic_bid_class = semanticbids.FourthSuitForcing
    priority = priorities.InvalidBid  # We do not yet know how to plan FSF.
    implied_constraints = {
        # FIXME: Should be at least 10 points since we're forcing the auction to the 3 level?
        '2S': [MaxLength(3)]
    }


class NotrumpResponseToFourthSuitForcing(Rule):
    preconditions = [PartnerLastBidWasFourthSuitForcing(), IsNotrump(), NotJumpFromLastContract()]
    # Implies a stopper in the FSF suit.
    # Unclear what point ranges?  Maybe just normal ones?  Should this be a logic rule?
    implied_constraints = {
        Rule.ANY_OTHER_BID: [StopperInFourthSuit()]
    }


class ControlBid(Rule):
    # Indicates first or second round control of a suit.
    # Denies control in skipped suits (except trump?)
    preconditions = [
        FitEstablishedInSomeSuit(),
        MinimumCombinedPointsPrecondition(25),
        PartnerLastBidWasContract(),
        NotJumpFromPartnerLastBid(),
        NotSuitWithFit(),
        SecondRoundControlIsNotKnown(),
    ]
    priority = priorities.InvalidBid  # We don't know how to plan these yet.
    implied_constraints = {
        Rule.ANY_OTHER_BID: [NoControlInSkippedSuits(), Control()]
    }


class Blackwood(Rule):
    preconditions = [PartnerLastBidWasNaturalSuit(), JumpOrHaveFit()]
    implied_constraints = {
        '4N': [],  # We just need to identify Blackwood
    }
    semantic_bid_class = semanticbids.Blackwood
    priority = priorities.InvalidBid  # We do not yet know how to plan Blackwood.


class BlackwoodForKings(Rule):
    preconditions = [MyLastBidWasBlackwood()]
    implied_constraints = {
        '5N': [],  # We just need to identify Blackwood
    }
    semantic_bid_class = semanticbids.Blackwood
    priority = priorities.InvalidBid  # We do not yet know how to plan Blackwood.


class BlackwoodResponse(Rule):
    # FIXME: These should be on over an RHO double.
    preconditions = [PartnerLastBidWasBlackwood(), RHOPassed(), NotJumpFromLastContract()]
    semantic_bid_class = semanticbids.Artificial
    implied_constraints = {
        '5C': [Aces(HandConstraints.ZERO_OR_FOUR)],
        '5D': [Aces(1)],
        '5H': [Aces(2)],
        '5S': [Aces(3)],

        '6C': [Kings(HandConstraints.ZERO_OR_FOUR)],
        '6D': [Kings(1)],
        '6H': [Kings(2)],
        '6S': [Kings(3)],
    }


class Gerber(Rule):
    # It's slightly unclear when Gerber is available. These conditions are relatively conservative.
    # This should probably be PartnerLastBidWasNaturalNotrump OR IsNotrumpProtocol()?
    preconditions = [PartnerLastBidWasNaturalNotrump()]
    implied_constraints = {
        '4C': [],  # We just need to identify Gerber
    }
    semantic_bid_class = semanticbids.Gerber
    priority = priorities.InvalidBid  # We do not yet know how to plan Gerber.


class GerberForKings(Rule):
    preconditions = [MyLastBidWasGerber()]
    implied_constraints = {
        '5C': [],  # We just need to identify Gerber
    }
    semantic_bid_class = semanticbids.Gerber
    priority = priorities.InvalidBid  # We do not yet know how to plan Gerber.


class GerberResponse(Rule):
    preconditions = [PartnerLastBidWasGerber(), RHOPassed(), NotJumpFromLastContract()]
    semantic_bid_class = semanticbids.Artificial
    implied_constraints = {
        '4D': [Aces(HandConstraints.ZERO_OR_FOUR)],
        '4H': [Aces(1)],
        '4S': [Aces(2)],
        '4N': [Aces(3)],

        '5D': [Kings(HandConstraints.ZERO_OR_FOUR)],
        '5H': [Kings(1)],
        '5S': [Kings(2)],
        '5N': [Kings(3)],
    }
