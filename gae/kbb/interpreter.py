# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import copy

from core.position import in_partnership_with
import kbb.rules as rules
from kbb.knowledge import Knowledge
from kbb.semanticbids import SemanticBid


import logging
_log = logging.getLogger(__name__)


class ConventionCard(object):
    # The default convention card is empty.
    static_logic_rules = []
    static_interpretation_rules = []

    def logic_rules(self):
        return self.static_logic_rules

    def interpretation_rules(self):
        return self.static_interpretation_rules


class StandardAmericanYellowCard(ConventionCard):
    # Logic rules never produce a bid, just may update the Knowledge, and need to
    # be applied before applying any other rules.
    static_logic_rules = [
        rules.CorrectStrongFourCardSuitLength(),
    ]

    # Order here is not about which bid to make, but rather what the most
    # specific interpretation of any given bid would be.  More specific
    # interpretations should occur before more generic ones.
    # For example, Reverse() should appear before NewSuit()
    # as a Reverse is a special kind of NewSuit which means more
    # than a normal NewSuit would.
    static_interpretation_rules = [
        rules.NotrumpResponseToFourthSuitForcing(),
        rules.BlackwoodResponse(),
        rules.GerberResponse(),
        rules.NotrumpRebidAfterJacobyTransfer(),
        rules.OtherMajorRebidAfterJacobyTransfer(),
        rules.NewMinorRebidAfterJacobyTransfer(),
        rules.ResponseToJacobyTransfer(), # Responses which make no sense are blocked.
        rules.ResponseToTwoSpadesPuppet(), # Responses which make no sense are blocked.
        rules.ResponseToTwoSpadesPuppetTransferAccept(), # 3D or P are the only valid bids.

        rules.NotrumpResponseToTakeoutDouble(),
        rules.CuebidResponseToTakeoutDouble(),
        rules.JumpSuitResponseToTakeoutDouble(),
        rules.SuitResponseToTakeoutDouble(),
        rules.RaiseAfterTakeoutDouble(),
        rules.JumpRaiseAfterTakeoutDouble(),
        rules.NewSuitAfterTakeoutDouble(),
        rules.JumpNewSuitAfterTakeoutDouble(),
        rules.NotrumpAfterTakeoutDouble(),
        rules.NonJumpTwoNotrumpAfterTakeoutDouble(),
        rules.JumpTwoNotrumpAfterTakeoutDouble(),
        rules.CueBidAfterTakeoutDouble(),
        rules.TakeoutDoubleAfterTakeoutDouble(),

        rules.RebidAfterUnusualNotrump(), # Amendes the knowledge point range, but does not consume the bid (except pass).
        rules.ResponseToStayman(),
        rules.DisallowAllStaymanResponses(),
        rules.ResponseToJacoby2N(),
        rules.WaitingResponseToStrongTwoClubs(),
        rules.SuitResponseToStrongTwoClubs(),
        rules.NotrumpResponseToStrongTwoClubs(),
        rules.SecondNegative(),

        rules.CueBidAfterNegativedDouble(),
        rules.TwoSpadesJumpFourthSuitForcing(),  # Must be higher priority than JumpShiftResponderRebid.
        rules.FourthSuitForcing(),  # This needs to be lower priority interpretation than Cuebids.

        rules.FourthSeatMajorOpen(),
        rules.FourthSeatMinorOpen(),

        # Conventional responses after a Stayman bid.
        rules.GarbageStaymanPass(),
        rules.MinorGameForceRebid(),
        rules.NotrumpRebidAfterStayman(),
        rules.OtherMajorRebidAfterStayman(),

        rules.NewSuitResponseToPreempt(),
        rules.TwoNotrumpFeatureRequest(),
        rules.MinimumSuitRebidResponseAfterPreempt(),
        rules.FeatureResponseToTwoNotrumpFeatureRequest(),

        rules.ControlBid(),

        # The remaining openings are exclusive, thus ordering should not matter.
        rules.NotrumpOpen(),
        rules.MajorOpen(),
        rules.MinorOpen(),
        rules.PreemptiveOpen(),
        rules.StrongTwoClubs(),

        rules.NotrumpJumpRebid(),
        rules.NotrumpRebidOverTwoClubs(),

        rules.NotrumpGameInvitation(),

        rules.StaymanNoCompetition(),
        rules.StaymanAfterRHODouble(),
        rules.StaymanAfterRHOClubOvercall(),

        rules.JacobyTransferNoCompetition(),
        rules.JacobyTransferAfterRHODouble(),
        rules.JacobyTransferAfterRHOClubOvercall(),

        rules.TwoSpadesPuppet(),
        rules.QuantitativeFourNotrumpJump(),
        rules.QuantitativeFiveNotrumpJump(),
        rules.Jacoby2N(),

        rules.LongMinorGameInvitation(),
        rules.LongMajorSlamInvitation(),

        rules.JumpResponseToMichaelsMinorRequest(),
        rules.NonJumpResponseToMichaelsMinorRequest(),
        rules.UnforcedMichaelsMinorRequest(),
        rules.MichaelsMinorRequest(),

        rules.Blackwood(),
        rules.BlackwoodForKings(),
        rules.Gerber(),
        rules.GerberForKings(),

        rules.OpenerSuitedRebidAfterStrongTwoClubs(),
        rules.OpenerSuitedJumpRebidAfterStrongTwoClubs(),  # After Gerber

        rules.ReopeningDouble(),  # Higher priority interpretation than BalancingTakeoutDouble (although they mean very similar things).

        rules.BalancingMichaelsCuebid(),
        rules.BalancingOvercallNotrump(),
        rules.BalancingSuitedOvercall(),
        rules.BalancingJumpOvercall(),
        rules.BalancingTakeoutDouble(),

        rules.DirectMichaelsCuebid(),  # Important this is before DirectSuitedOvercall and after CueBidAfterNegativedDouble.
        rules.UnusualNotrump(),
        rules.UnusualNotrumpOverTwoClubs(),

        rules.DirectSuitedOvercall(),
        rules.DirectPreemptiveOvercall(),
        rules.DirectNotrumpOvercall(),
        rules.DirectNotrumpDouble(),

        rules.IndirectSuitedOvercall(),
        rules.IndirectPreemptiveOvercall(),
        rules.IndirectNotrumpOvercall(),
        # FIXME: Need IndirectMichaelsCuebid (when the opponents have only bid one suit).

        rules.NegativeDouble(),
        rules.LeadDirectingDouble(),

        rules.OneLevelTakeoutDouble(),
        rules.TwoLevelTakeoutDouble(),
        rules.TakeoutDoubleAfterPreempt(),

        rules.PenaltyDoubleOfSuit(),
        rules.PenaltyDoubleOfNotrump(),

        rules.GenericTakeoutDouble(),  # Important to be low-priority, as it adds no constraints.

        rules.JumpShiftResponseToOpenAfterRHODouble(),
        rules.JumpShiftByOpener(),
        rules.JumpShiftResponseToOpen(),
        rules.JumpShiftResponderRebid(),

        rules.OpenerReverse(),
        rules.ResponderReverse(),

        # Intentionally after Reverse/JumpShift.
        rules.NewOneLevelMajorByOpener(),
        rules.HelpSuitGameTry(),
        rules.NewSuitByOpener(),
        rules.OpenerRebidAfterLimitRaise(),
        rules.RebidOriginalSuitByOpener(),
        rules.JumpRebidOriginalSuitByOpener(),
        rules.DoubleJumpRebidByOpener(),
        rules.InviteByRaisingSuit(),
        rules.NotrumpInvitationByOpener(),
        rules.RaisePartnersSuit(),

        rules.RedoubleResponseToMajorAfterRHOTakeoutDouble(),
        rules.JumpRaiseResponseToMajorOpenAfterRHOTakeoutDouble(),
        rules.JumpRaiseResponseToMinorOpenAfterRHOTakeoutDouble(),

        rules.JordanResponseToMinor(),
        rules.JordanResponseToMajor(),

        rules.NotrumpJumpOverMinor(),
        rules.MinimumRaiseResponseToMinorOpen(),
        rules.MinimumRaiseResponseToMajorOpen(),
        rules.JumpRaiseResponseToMajorOpen(),
        rules.GameJumpRaiseResponseToMajorOpen(),

        rules.ResponderSignoffInPartnersSuit(),
        rules.ThreeLevelSuitRebidByResponder(),
        rules.RebidResponderSuitByResponder(),
        rules.DelayedNewSuitByResponder(),  # Must be after ResponderSignoffInPartnersSuit.
        rules.ResponderSignoffInMinorGame(),

        rules.NewOneLevelSuitByResponderNoCompetition(),
        rules.NewOneLevelSuitByResponderAfterRHOOneDiamonds(),
        rules.NewOneLevelSuitByResponderInCompetition(),
        rules.NewTwoLevelSuitByResponder(),
        rules.NewThreeLevelSuitByResponder(),

        rules.DelayedSupportByOpener(),

        # FIXME: This should be a relatively high priority interpretation
        # When we're forced to bid, we're allowed to escape to his suit with nothing.
        rules.EscapeToSuitedContract(),
        rules.EscapeToBetterPartScore(),

        rules.CheapestNotrumpByOpener(),
        rules.CheapestNotrumpByResponder(),

        rules.NewSuitResponseToOvercall(),
        rules.RaiseResponseToDirectOvercall(),
        rules.JumpRaiseResponseToDirectOvercall(),
        rules.CuebidResponseToDirectOvercall(),

        rules.MajorGame(),
        rules.MinorGame(),
        rules.SuitedToPlay(),
        rules.NotrumpWithoutStoppers(),
        rules.EscapeToNotrumpGame(),
        rules.NotrumpGame(),
        rules.NotrumpSlam(),
        rules.NotrumpToPlay(),

        # FIXME: Add more better logic for handling preempts.
        # rules.QuickTrickResponseToPreempt(),

        # Note: This is intentionally a lower priority interpretation
        # than the point-based calculations SuitedToPlay.
        rules.LawOfTotalTricks(),

        rules.FourthSeatOpeningPass(),
        rules.OpeningPass(),
        rules.DirectOvercallPass(),
        rules.IndirectOvercallPass(),
        rules.PassResponseToOneLevelSuitedOpen(),
        rules.PassAfterTakeoutDouble(),
        rules.SuitGameIsRemote(),
        rules.NotrumpGameIsRemote(),
        rules.SuitSlamIsRemote(),
        rules.NotrumpSlamIsRemote(),
        rules.DefaultPass(),
    ]


class KnowledgeBuilder(object):
    def __init__(self):
        self.bid_rule_tuples = []

    # The idea is that we're saving the rules so that we can quickly re-render the knowledge.
    # There is some thought of later swapping out rules, or modifying rules after the fact.

    def render_knowledge(self):
        knowledge = Knowledge()
        for bid, rule in self.bid_rule_tuples:
            if rule:
                knowledge, consumed_bid = rule.apply(knowledge, bid)
                assert consumed_bid, "Cached rule in KnowledgeBuilder did not consume bid?"
                knowledge.me.last_call = rule.semantic_bid(bid)
            else:
                knowledge.me.last_call = SemanticBid(bid.name)

            knowledge.rotate()
        return knowledge

    def record_bid(self, bid, rule):
        bid_rule_tuple = (bid, rule)
        self.bid_rule_tuples.append(bid_rule_tuple)

    def bids(self):
        bids, _ = zip(*self.bid_rule_tuples)
        return bids

    def matched_rules(self):
        _, matched_rules = zip(*self.bid_rule_tuples)
        return matched_rules


# This knows how to create knowledge from bid histories.
class BidInterpreter(object):
    def __init__(self):
        self.our_conventions = StandardAmericanYellowCard()
        self.their_conventions = self.our_conventions # FIXME: For now use the same rules.

    def _apply_rules(self, rules, knowledge, new_bid, loose_constraints=None):
        for rule in rules:
            #_log.debug("Checking %s, %s" % (rule, new_bid))
            try:
                knowledge, consumed_bid = rule.apply(knowledge, new_bid)
            except AssertionError:
                _log.warn("Assertion applying rule %s matching bid %s to knowledge: %s" % (rule, new_bid, knowledge))
                if loose_constraints:
                    raise
                return None, None
            if not knowledge:
                #_log.debug("%s matched bid %s and returned None for knowledge." % (rule, new_bid))
                return None, None
            if not loose_constraints and not knowledge.me.is_valid():
                # We found a rule, but it produced invalid hand constraints, so it's a meaningless interpretation.
                _log.warn("Rule %s for bid %s resulted in invalid knowledge: %s" % (rule, new_bid, knowledge))
                return None, None
            if consumed_bid:
                #_log.debug("%s matched %s, new knowledge: %s" % (rule, new_bid, knowledge))
                knowledge.me.last_call = rule.semantic_bid(new_bid)
                return knowledge, rule
        # Did not consume the bid, but may have updated the knowledge (logic rules).
        return knowledge, None

    def knowledge_including_new_bid(self, knowledge_builder, new_bid, convention_card=None, loose_constraints=None):
        knowledge = knowledge_builder.render_knowledge()

        convention_card = convention_card or self.our_conventions
        knowledge, consuming_rule = self._apply_rules(convention_card.logic_rules(), knowledge, new_bid, loose_constraints)
        assert not consuming_rule, "Knowedge rules should never consume the bid!"
        knowledge, consuming_rule = self._apply_rules(convention_card.interpretation_rules(), knowledge, new_bid, loose_constraints)

        # FIXME: Why is this if statement needed?
        if not consuming_rule:
            #_log.debug("Failed to match any rule for: %s" % (new_bid))
            return None, None
        return knowledge, consuming_rule

    def knowledge_from_history(self, history, loose_constraints=None):
        # Intentionally holding the viewer outside of the knowledge.
        viewer = history.position_to_call()
        knowledge_builder = KnowledgeBuilder()

        # FIXME: This should use some sort of history.enumerate_calls_and_bidders() method.
        for partial_history in history.ascending_partial_histories(step=1):
            bid = partial_history.last_call()
            bidder = partial_history.last_to_call()

            convention_card = self.our_conventions if in_partnership_with(bidder, viewer) else self.their_conventions
            _, consuming_rule = self.knowledge_including_new_bid(knowledge_builder, bid, convention_card=convention_card, loose_constraints=loose_constraints)
            knowledge_builder.record_bid(bid, consuming_rule)

        return knowledge_builder.render_knowledge(), knowledge_builder
