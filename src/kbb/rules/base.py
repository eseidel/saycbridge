# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from kbb.bidding_priorities import priorities
from kbb.constraints import *
from kbb.handconstraints import HonorConstraint, HandConstraints
from kbb.knowledge import point_systems
from kbb.preconditions import *
from kbb import semanticbids


import logging
_log = logging.getLogger(__name__)


class Rule(object):
    preconditions = []
    implied_constraints = None
    shared_implied_constraints = []
    # FIXME: Currently the explorer shows blank for bids with Default priority
    # because we can't tell the difference between Default priority bids and
    # bids with a complicated priority_for_bid implementation.
    priority = None
    point_system = None
    semantic_bid_class = None
    explanation = None
    sayc_page = None

    LEVEL_1 = 1
    LEVEL_2 = 2
    LEVEL_3 = 3
    LEVEL_4 = 4
    LEVEL_5 = 5
    LEVEL_6 = 6
    LEVEL_7 = 7

    CLUBS = strain_char(CLUBS)
    DIAMONDS = strain_char(DIAMONDS)
    HEARTS = strain_char(HEARTS)
    SPADES = strain_char(SPADES)
    NOTRUMP = strain_char(NOTRUMP)

    ANY_OTHER_BID = '*'

    @property
    def name(self):
        return self.__class__.__name__

    def __repr__(self):
        return "%s()" % self.name

    # Rules map knowledge, bid pairs to knowledge, bid pairs.
    # Normally rules consume the bid, adding it to the knowledge object.
    def apply(self, knowledge, bid):
        for condition in self.preconditions:
            if not condition.fits(knowledge, bid):
                #_log.debug("%s does not fit %s for %s" % (condition, bid, self))
                return knowledge, False

        new_knowledge = self.consume_call(knowledge, bid)
        # To make consume_call easier to implement we allow the value False to mean
        # "I don't apply to this".
        if new_knowledge == False:
            #_log.debug("%s does not apply to %s, consume_call returned False" % (self, bid))
            return knowledge, False
        return new_knowledge, True

    # Subclasses may want to override this or apply() to provide custom behavior.
    def consume_call(self, knowledge, call):
        constraints = self.implied_constraints.get(call.name)
        if constraints is None and call.strain:
            constraints = self.implied_constraints.get(strain_char(call.strain))
        if constraints is None:
            constraints = self.implied_constraints.get(call.level())
        if constraints is None:
            constraints = self.implied_constraints.get(self.ANY_OTHER_BID)
        if constraints is None:
            return False
        # Note: We're careful not to modify the constraints we get from self.implied_constraints.
        constraints = constraints + self.shared_implied_constraints
        for constraint in constraints:
            constraint.apply_to(knowledge, call)
        return knowledge

    def semantic_bid(self, bid):
        bid_class = self.semantic_bid_class or semanticbids.SemanticBid
        return bid_class(bid.name)

    def priority_for_bid(self, hand, bid):
        if self.priority is None:
            return priorities.Default
        return self.priority

    def explanation_for_bid(self, bid):
        return self.explanation

    def sayc_page_for_bid(self, bid):
        return self.sayc_page

    def point_system_for_bid(self, bid):
        if self.point_system is None:
            # Default to HighCardPoints unless specified otherwise.
            return point_systems.HighCardPoints
        return self.point_system


class Opening(Rule):
    preconditions = Rule.preconditions + [NoOpening()]
    shared_implied_constraints = Rule.shared_implied_constraints + [SetOpened()]
    semantic_bid_class = semanticbids.Opening


class OpeningResponse(Rule):
    preconditions = Rule.preconditions + [PartnerLastBidWasOpen()]


class ResponseToOneLevelSuitedOpen(OpeningResponse):
    preconditions = OpeningResponse.preconditions + [PartnerLastBidWasLevel(1), PartnerLastBidWasNaturalSuit()]


class OpenerRebid(Rule):
    preconditions = Rule.preconditions + [MyLastBidWasOpen()]


# Note this is not an Opening, as we don't want to set opened = True.
class OpeningPass(Rule):
    preconditions = Rule.preconditions + [NoOpening()]
    priority = priorities.Pass

    implied_constraints = {
        'P': [RuleOfTwenty(False), HighCardPointRange(0, 12)],
    }


class FourthSeatOpeningPass(Rule):
    preconditions = Rule.preconditions + [NoOpening(), FourthSeat()]
    priority = priorities.Pass

    implied_constraints = {
        'P': [RuleOfFifteen(False)],
    }


class PassRule(Rule):
    preconditions = Rule.preconditions + [IsPass(), NotForcedToBid()]


class DefaultPass(PassRule):
    priority = priorities.Pass
    implied_constraints = {
        'P': [],
    }
    explanation = "No information gained from this pass."


class NotrumpGameIsRemote(PassRule):
    preconditions = PassRule.preconditions + [RHOPassed(), PartnerLastBidWasNaturalNotrump(), LastBidWasBelowGame()]
    priority = priorities.SettleForNotrumpPartScore
    point_system = point_systems.NotrumpSupport
    implied_constraints = {
        'P': [MaximumCombinedPoints(24)],
    }


class SuitGameIsRemote(PassRule):
    preconditions = PassRule.preconditions + [RHOPassed(), PartnerLastBidWasNaturalSuit(), LastBidWasBelowGame()]
    priority = priorities.SettleForSuitedPartScore
    # FIXME: Should this use support points?
    implied_constraints = {
        # FIXME: The bot can interpret a None-Pass as implying 7+ in the suit bid wasn't understood.
        'P': [MinimumCombinedLength(7, use_last_call_suit=True), MaximumCombinedPoints(24)],
    }


class SuitSlamIsRemote(PassRule):
    # FIXME: This should only apply if last bid was a suit we have a fit in, right?
    preconditions = PassRule.preconditions + [RHOPassed(), PartnerLastBidWasNaturalSuit(), LastBidWasGameOrAbove()]
    priority = priorities.SettleForGame
    point_system = point_systems.SupportPointsIfFit
    implied_constraints = {
        'P': [MinimumCombinedLength(7, use_last_call_suit=True), MaximumCombinedPoints(32)],
    }


class NotrumpSlamIsRemote(PassRule):
    preconditions = PassRule.preconditions + [RHOPassed(), PartnerLastBidWasNaturalNotrump(), LastBidWasGameOrAbove()]
    priority = priorities.SettleForGame
    point_system = point_systems.NotrumpSupport
    implied_constraints = {
        'P': [MaximumCombinedPoints(32)],
    }


# FIXME: We need a SacraficeLawOfTotalTricks()
class LawOfTotalTricks(Rule):
    # This rule only applies when we don't have enough points
    # to make PointBasedRule calculations.
    # FIXME: But when is that exactly? Responses to Preempts, Responses to Overcalls?  What about responses to Balancing doubles?
    # Are Law of TotalTricks bids always sacrifices?
    # Sum of their holding + you holding, bid that number - 6.
    # FIXME: Perhaps this should require that someone already opened the auction?
    preconditions = Rule.preconditions + [NotOpened(), IsSuit(), GameOrBelow(), PartnershipBidSuit()]
    priority = priorities.LawOfTotalTricks
    implied_constraints = {
        # FIXME: We need to give this some point cap, or it's effectively forcing.
        # With 17 points seems like we'd have some other bid.
        Rule.ANY_OTHER_BID: [LengthSatisfiesLawOfTotalTricks(), MaxHighCardPoints(17)],
    }


class PenaltyDoubleOfSuit(Rule):
    preconditions = Rule.preconditions + [LastBidWasSuit(), LastBidWasGameOrAbove()]
    # FIXME: Penalty doubles are actually high priority bids as long as we understand when to make them.
    priority = priorities.InvalidBid
    semantic_bid_class = semanticbids.PenaltyDouble
    implied_constraints = {
        # FIXME: This should probably imply some number of quick tricks.
        'X': []
    }


class PenaltyDoubleOfNotrump(Rule):
    preconditions = Rule.preconditions + [LastBidWasNotrump()]
    # FIXME: Penalty doubles are actually high priority bids as long as we understand when to make them.
    priority = priorities.InvalidBid
    semantic_bid_class = semanticbids.PenaltyDouble
    implied_constraints = {
        # FIXME: This should probably imply some amount of trick-taking potential.
        'X': []
    }


class NotrumpWithoutStoppers(Rule):
    # We should only be bidding NT w/o stoppers as a last resort (when we're forced to bid).
    preconditions = Rule.preconditions + [NotJumpFromLastContract(), ForcedToBid()]
    priority = priorities.NotrumpWithoutStoppers

    implied_constraints = {
        # FIXME: Why is this 19, and not 18?  1C P 1N is CheapestNotrumpByResponder and shows only 6 points?
        '1N': [CombinedPointRangeOverPartnerMinimum(19, 21)],
        '2N': [CombinedPointRangeOverPartnerMinimum(22, 24)],
    }
    shared_implied_constraints = [NoMajorFit(), StoppersInOpponentsSuits()]


class EscapeToNotrumpGame(Rule):
    preconditions = Rule.preconditions + [NotJumpFromLastContract(), LastBidWasSuit()]
    priority = priorities.NotrumpGame

    implied_constraints = {
        '3N': [CombinedPointRangeOverPartnerMinimum(25, 29), NoMajorFit(), StoppersInOpponentsSuits()],
    }


class EscapeToSuitedContract(Rule):
    # Note, this only applies to bidding partner's suit.
    preconditions = Rule.preconditions + [ForcedToBid(), NotJumpFromLastContract(), IsSuit(), PartnerHasAtLeastCountInSuit(3), NotSameSuitAsLastContract(), BelowGame()]
    priority = priorities.EscapeToSuitedContract
    implied_constraints = {
        # FIXME: It's not so much that we have a fit with partner, so much
        # as that we believe this is our best (possibly bad) option.
        Rule.ANY_OTHER_BID: [MinimumCombinedLength(7)],
    }


# This rule only covers the case where Partner's last bid was not a fit and
# we need to escape to something better below game.
class EscapeToBetterPartScore(Rule):
    preconditions = Rule.preconditions + [RHOPassed(), SameLevelAsLastContract(), BelowGame(), PartnershipBidSuit(), PartnerLastBidWasContract()]
    priority = priorities.EscapeToSuitedContract
    implied_constraints = {
        Rule.LEVEL_2: [CombinedPointRangeOverPartnerMinimum(19, 24)],
        Rule.LEVEL_3: [CombinedPointRangeOverPartnerMinimum(22, 24)],
        Rule.LEVEL_4: [CombinedPointRangeOverPartnerMinimum(25, 27)],
    }
    shared_implied_constraints = [BetterFitThanPartnerLastContract()]


class NotrumpToPlay(Rule):
    point_system = point_systems.NotrumpSupport
    priority = priorities.NotrumpToPlay

    implied_constraints = {
        '1N': [CombinedPointRangeOverPartnerMinimum(19, 21), StoppersInUnbidSuits()],
        '2N': [CombinedPointRangeOverPartnerMinimum(22, 24), StoppersInUnbidSuits()],
        # 3N is NotrumpGame with higher priority.

        # 4N is often reserved for special bids. It's point range is folded into 3N
        # In some cases, 4N is actually natural and not Blackwood. In those cases,
        # 3N is not available, so 4N inherits its point range.
        # FIXME: When is this?  Should this only be a non-jump rule?  Seems jumping to 4N never makes sense.
        '4N': [CombinedPointRangeOverPartnerMinimum(25, 29), StoppersInUnbidSuits()],

        # If you've got 30 points between you, you have all the suits stopped, even if the bidding doesn't show it.
        '5N': [CombinedPointRangeOverPartnerMinimum(30, 32)],
    }


class NotrumpGame(Rule):
    point_system = point_systems.NotrumpSupport
    priority = priorities.NotrumpGame
    implied_constraints = {
        # Note: We allow up to 30 points (when jumping) as 5N is QuantitativeNotrumpJump and requires 31-32.
        '3N': [CombinedPointRangeOverPartnerMinimum(25, 30), StoppersInUnbidSuits()],
    }


class NotrumpSlam(Rule):
    priority = priorities.NotrumpSlam
    implied_constraints = {
        # If you have 33 points between you, you have all the suits stopped, even if the bidding doesn't show it.
        '6N': [CombinedPointRangeOverPartnerMinimum(33, 36)],
        '7N': [CombinedPointRangeOverPartnerMinimum(37, 40)],
    }


class SuitedToPlay(Rule):
    # FIXME: This won't match 4th seat opens, as those only show 10 points.
    # FIXME: Should this be PartnershipBidSuit?
    preconditions = [MinimumCombinedPointsPrecondition(12), PartnerHasAtLeastCountInSuit(1)]
    point_system = point_systems.SupportPointsIfFit
    priority = priorities.SuitedToPlay

    implied_constraints = {
        Rule.LEVEL_2: [CombinedPointRangeOverPartnerMinimum(19, 21)],
        Rule.LEVEL_3: [CombinedPointRangeOverPartnerMinimum(22, 24)],

        '4C': [CombinedPointRangeOverPartnerMinimum(25, 27)],
        '4D': [CombinedPointRangeOverPartnerMinimum(25, 27)],

        Rule.LEVEL_6: [CombinedPointRangeOverPartnerMinimum(33, 36)],
        Rule.LEVEL_7: [CombinedPointRangeOverPartnerMinimum(37, 40)],
    }

    shared_implied_constraints = [MinimumCombinedLength(8)]


class MajorGame(SuitedToPlay):
    priority = priorities.MajorGame
    point_system = point_systems.SupportPointsIfFit
    implied_constraints = {
        '4H': [CombinedPointRangeOverPartnerMinimum(25, 32)],
        '4S': [CombinedPointRangeOverPartnerMinimum(25, 32)],
    }


class MinorGame(SuitedToPlay):
    priority = priorities.MinorGame
    point_system = point_systems.SupportPointsIfFit
    implied_constraints = {
        '5C': [CombinedPointRangeOverPartnerMinimum(28, 32)],
        '5D': [CombinedPointRangeOverPartnerMinimum(28, 32)],
    }
