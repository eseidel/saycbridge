from core.callexplorer import CallExplorer
from core.suit import *
from kbb.handconstraints import HonorConstraint, HandConstraints
from kbb.interpreter import BidInterpreter
from kbb.knowledge import point_systems
from kbb.bidding_priorities import priorities

import logging
_log = logging.getLogger(__name__)


# This only answers the question "is this knowledge + new_bid consistent with this hand"
class ConsistencyOracle(object):
    def __init__(self, history, hand):
        self.interpreter = BidInterpreter()
        self.existing_knowledge, self.knowledge_builder = self.interpreter.knowledge_from_history(history)
        self.hand = hand
        assert self.existing_knowledge, "Oracle can't understant existing history: %s" % history

    def _is_rule_of_twenty(self, hand):
        two_longest_suits = sorted(hand.suit_lengths())[-2:]
        return sum(two_longest_suits) + hand.high_card_points() >= 20

    def _is_rule_of_fifteen(self, hand):
        return hand.length_of_suit(SPADES) + hand.high_card_points() >= 15

    def _is_garbage_stayman(self, hand):
        if hand.high_card_points() > 7:
            return False
        # We can have at fewest 4 diamonds or 3 of either major.
        # That gaurentees at least a (rare!) 6 card diamond fit, or 7 card major fit.
        for suit in MAJORS:
            # If we have a 5 card major we should escape transfer to it instead.
            if hand.length_of_suit(suit) not in (3, 4):
                return False
        if hand.length_of_suit(DIAMONDS) < 4:
            return False
        return True

    def _is_minor_game_force_stayman(self, hand):
        if hand.high_card_points() < 13: # 15 + 13 = 28
            return False
        if hand.length_of_suit(CLUBS) >= 6 or hand.length_of_suit(DIAMONDS) >= 6:
            return True
        # FIXME: Should promise 3o5 or 2o3 in the Minor?
        return False

    def _should_bid_stayman(self, knowledge, hand):
        # FIXME: GarbageStayman and MinorGameForceStayman are only valid over 1N openings.
        if knowledge.partner.last_call.level() == 1:
            if self._is_garbage_stayman(hand):
                return True
            if self._is_minor_game_force_stayman(hand):
                return True
        # Otherwise Stayman promises a 4-card major and 8+ points (over 1N).
        major_lengths = tuple(hand.suit_lengths()[-2:])
        if 4 not in major_lengths:
            return False
        return True # Promised points will be enforced normally in the point check.

    def _can_big_hand_double(self, hand):
        # p118 says not to plan a big-hand double with a two suited hand.
        long_suit_count = 0
        for suit in SUITS:
            if hand.length_of_suit(suit) >= 5:
                long_suit_count += 1
        if long_suit_count >= 2:
            return False
        return hand.high_card_points() >= 17

    def _have_shape_for_two_spades_puppet(self, hand):
        return hand.length_of_suit(CLUBS) >= 6 or hand.length_of_suit(DIAMONDS) >= 6

    def _have_unspecified_minor_for_michaels_cuebid_of_a_major(self, hand):
        for suit in MINORS:
            if hand.length_of_suit(suit) >= 5:
                return True
        return False

    def _trump_suit(self, knowledge):
        suit_fits = filter(lambda suit: (knowledge.me.min_length(suit) + knowledge.partner.min_length(suit)) >= 8, SUITS)
        if len(suit_fits) == 1:
            return suit_fits[0]
        # If the bid we're considering making happens to be one of the suits we have a fit with partner in
        # then we'll assume that's the suit we should use to count support points.
        if knowledge.me.last_call.strain in suit_fits:
            return knowledge.me.last_call.strain
        if len(suit_fits) > 1:
            # Would be nice to log here, but we hit this way too often for crazy bids over takeout doubles or NT openings.
            #_log.warn("Multiple suit fits %s, unsure what point system to use, using LengthPoints." % map(suit_name, suit_fits))
            return None
        _log.warn("Unable to find suit fit, yet fit-requring point system used!  Rule error?")
        return None

    def _points_for_hand(self, hand, point_system, knowledge):
        if point_system == point_systems.HighCardPoints:
            return hand.high_card_points()
        if point_system == point_systems.NotrumpSupport:
            # When bidding for a NT auction, we deduct one point for a flat hand.
            return hand.high_card_points() - 1 if hand.is_flat() else hand.high_card_points()
        if point_system == point_systems.SupportPointsIfFit:
            trump_suit = self._trump_suit(knowledge)
            if trump_suit is not None:
                our_trump_count = hand.length_of_suit(trump_suit)
                partners_trump_count = knowledge.partner.min_length(trump_suit)
                if our_trump_count < partners_trump_count:
                    return hand.support_points(trump_suit)
                # It's somewhat unclear to me when we should count support points
                # when the trumps are split evenly.  This appears to be required
                # for some of the examples in the book.  This is a somewhat conservative
                # first approximation.
                if (trump_suit in MAJORS and
                    our_trump_count == partners_trump_count and our_trump_count == 4 and
                    knowledge.partner.median_hcp() > hand.high_card_points() and
                    not knowledge.partner.notrump_protocol):
                    return hand.support_points(trump_suit)
            # SupportPointsIfFit falls back to LengthPoints if there is no fit.
            return hand.length_points()

        # Make sure we never add a point system enum without adding actual support for it.
        assert point_system == point_systems.LengthPoints
        return hand.length_points()

    def _points_fit_knowledge(self, hand, point_system, knowledge):
        # Ignore point checks for garbage stayman.
        # FIXME: There must be a better way to do this!
        if knowledge.partner.last_call and knowledge.partner.last_call.name == '1N' and knowledge.me.last_call.name == '2C':
            if self._is_garbage_stayman(hand):
                return True

        points = self._points_for_hand(hand, point_system, knowledge)
        hand_knowledge = knowledge.me

        # The rule of twenty overrides normal point checks for an opening bid.
        if hand_knowledge.rule_of_twenty is not None:
            if hand_knowledge.rule_of_twenty != self._is_rule_of_twenty(hand):
                return False
            # We can't just return True here, or we'd be short-circuting all
            # point range checks ever made against this hand.  To make sure
            # that the opening point range check passes, we'll just pretend
            # that any hand passing Ro20 has 12 playing points
            # (it does as length_points, but using length_points here would
            # cause 21 hcp hands to fail to open!).
            if hand_knowledge.rule_of_twenty:
                points = max(12, points)

        # Rule of Fifteen uses similar magic to Rule of Twenty, above.
        if hand_knowledge.rule_of_fifteen is not None:
            if hand_knowledge.rule_of_fifteen != self._is_rule_of_fifteen(hand):
                return False
            if hand_knowledge.rule_of_fifteen:
                points = max(10, points)

        if points not in hand_knowledge.hcp_range():
            return False
        return True

    def _honors_match_suit(self, honors, hand, suit):
        if honors == HonorConstraint.TWO_OF_TOP_THREE and not hand.has_at_least(2, 'AKQ', suit):
            return False
        # FIXME: This could be expressed more concisely!  Expecting 3o5 is always satisfied by having 2o3.
        if honors == HonorConstraint.THREE_OF_TOP_FIVE and not (hand.has_at_least(3, 'AKQJT', suit) or hand.has_at_least(2, 'AKQ', suit)):
            return False
        # We don't need to check "or 2o3 or 3o5" here since has_fourth_round_stopper recognizes Qxx as stopped.
        if honors == HonorConstraint.FOURTH_ROUND_STOPPER and not hand.has_fourth_round_stopper(suit):
            return False
        if honors == HonorConstraint.THIRD_ROUND_STOPPER and not hand.has_third_round_stopper(suit):
            return False
        return True

    def _matches_strong_four_card_suit_exception(self, hand, hand_knowledge, suit):
        length_in_suit = hand.length_of_suit(suit)
        # If our last bid was an overcalls, we're allowed to lie about
        # having five cards and bid a "good" four-card suit. The logic
        # rule CorrectOneLevelOvercallSuitLength will unwind this lie
        # after our partner has had a chance to respond.
        if not hand_knowledge.could_be_strong_four_card(suit):
            return False
        if length_in_suit < 4:
            return False
        assert length_in_suit == 4
        if not hand.has_at_least(2, 'AKQ', suit):
            return False
        return True

    def _shape_fits_hand_knowledge(self, hand, hand_knowledge):
        for suit in SUITS:
            length_in_suit = hand.length_of_suit(suit)
            if length_in_suit not in hand_knowledge.length_range(suit):
                if not self._matches_strong_four_card_suit_exception(hand, hand_knowledge, suit):
                    return False
            if not self._honors_match_suit(hand_knowledge.min_honors(suit), hand, suit):
                return False
            if hand_knowledge.longest_suit() == suit and not hand.is_longest_suit(suit, except_suits=hand_knowledge.longest_suit_exceptions()):
                return False
        if hand_knowledge.is_balanced():
            # We only have to check that the hand doesn't have more than one doubleton,
            # as the lengths check above catches suits outside of the 2-5 card range.
            if hand.suit_lengths().count(2) > 1:
                return False
        if hand_knowledge.last_call.takeout_double:
            # We only have to check that the hand doesn't have more than one tripleton,
            # as the lengths check above catches suits outside of expected ranges.
            # p98, h1 (as well as a bunch of misc_hands_from_play) seem to want this check.
            # I think this is to avoid having partner choose the suit when you clearly must
            # have a 5card suit of your own to mention.  If your suit is a major, you definitely
            # want to mention it to find the better fit.  If it's a minor, then your 3-card majors
            # are great support only if he has a 5-card major to mention himself, right?
            # FIXME: This doesn't seem right above the one level.  It's often that you can't overcall
            # at the 3 level.
            if hand.suit_lengths().count(3) > 1:
                return False
        return True

    def _fits_honor_count_constraints(self, hand, hand_knowledge):
        if hand_knowledge.ace_constraint() is not None:
            ace_constraint = hand_knowledge.ace_constraint()
            if ace_constraint == HandConstraints.ZERO_OR_FOUR:
                if hand.ace_count() != 0 and hand.ace_count() != 4:
                    return False
            elif hand.ace_count() != ace_constraint:
                return False
        if hand_knowledge.king_constraint() is not None:
            king_constraint = hand_knowledge.king_constraint()
            if king_constraint == HandConstraints.ZERO_OR_FOUR:
                if hand.king_count() != 0 and hand.king_count() != 4:
                    return False
            elif hand.king_count() != king_constraint:
                return False
        return True

    # FIXME: The knowledge object should include a list of hand expectation objects
    # and those expectations should be able to match themselves against a hand.
    # This current hard-coded solution will not scale long-term.
    def _knowledge_is_consistent_with_hand(self, knowledge, point_system, hand):
        hand_knowledge = knowledge.me
        if hand_knowledge.last_call.stayman and not self._should_bid_stayman(knowledge, hand):
            return False
        if hand_knowledge.last_call.two_spades_puppet and not self._have_shape_for_two_spades_puppet(hand):
            return False
        if hand_knowledge.last_call.michaels_cuebid and hand_knowledge.last_call.strain in MAJORS and not self._have_unspecified_minor_for_michaels_cuebid_of_a_major(hand):
            return False
        if hand_knowledge.last_call.takeout_double:
            # FIXME: The min_hcp() < 17 check is to prevent us from planning a big-hand double
            # (ignoring the rest of the hand shape), after a previous big-hand double.
            if hand_knowledge.min_hcp() < 17 and self._can_big_hand_double(hand):
                return True  # Notice that we short-circuit all the remaining constraints when planning a big-hand double.
        if not self._points_fit_knowledge(hand, point_system, knowledge):
            return False
        if not self._shape_fits_hand_knowledge(hand, hand_knowledge):
            return False
        if not self._fits_honor_count_constraints(hand, hand_knowledge):
            return False
        if hand_knowledge.quick_tricks() is not None:
            partner_min_lengths = [knowledge.partner.min_length(suit) for suit in SUITS]
            if hand.tricks(partner_min_lengths) < hand_knowledge.quick_tricks():
                return False
        # FIXME: We should check the hand against longer_major, longer_minor, longest_suit
        # being careful to ignore longest_suit_except.
        return True

    def priority_bid_rule_hand_knowledge_tuples(self, new_bid):
        # Note: This method is only ever called for evaluating bids with our own hand, otherwise we'd need to explicitly choose the correct rules.
        new_knowledge, consuming_rule = self.interpreter.knowledge_including_new_bid(self.knowledge_builder, new_bid, loose_constraints=True)
        if not new_knowledge:
            return priorities.InvalidBid, new_bid, consuming_rule, None
        point_system = consuming_rule.point_system_for_bid(new_bid)
        if not self._knowledge_is_consistent_with_hand(new_knowledge, point_system, self.hand):
            return priorities.InvalidBid, new_bid, consuming_rule, new_knowledge.me
        # Once we know that a bid is consistent with the hand, we then
        # lookup the bidding priority for the bid.  This is different
        # from the "interpretation" priority which is implicit
        # in the rule ordering in BidInterpreter.partner_rules.
        return consuming_rule.priority_for_bid(self.hand, new_bid), new_bid, consuming_rule, new_knowledge.me


class KnowledgeBasedBidder(object):
    def __init__(self):
        self.explorer = CallExplorer()

    def find_call_for(self, hand, history):
        bid, rule, hand_knowledge = self.find_bid_and_rule_and_hand_knowledge_for(hand, history)
        return bid

    def find_bid_and_rule_and_hand_knowledge_for(self, hand, history):
        oracle = ConsistencyOracle(history, hand)
        prioritiy_bid_rule_hand_knowledge_tuples = [oracle.priority_bid_rule_hand_knowledge_tuples(bid) for bid in self.explorer.possible_calls_over(history)]
        if not prioritiy_bid_rule_hand_knowledge_tuples:
            # We've exhausted all possible bids.  This could only happen over 7NT-redoubled.
            # FIXME: This could become an OutOfSpacePass instead of being a manual hack here?
            assert history.last_contract().name == '7N' and history.last_non_pass().is_redouble()
            return Pass(), None, oracle.existing_knowledge.me

        all_priorities, _, _, _ = zip(*prioritiy_bid_rule_hand_knowledge_tuples)
        highest_priority = min(all_priorities)
        if highest_priority == priorities.InvalidBid:
            # Everything we found was invalid, we have nothing to say, sorry.
            # FIXME: Eventually we'll want to _log.warn here.
            return None, None, oracle.existing_knowledge.me

        highest_priority_tuples = [priority_tuple for priority_tuple in prioritiy_bid_rule_hand_knowledge_tuples if priority_tuple[0] == highest_priority]
        if len(highest_priority_tuples) > 1:
            bid_and_rule_strings = ["%s from %s" % (bid, rule) for _, bid, rule, _ in highest_priority_tuples]
            _log.warn("Multiple bids of priority %s:  %s  Choosing highest: %s" % (highest_priority, bid_and_rule_strings, highest_priority_tuples[-1][1]))
        # The knowledge based bidder should always use the exact same rule for bidding as it would for interpret
        priority, bid, rule, hand_knowledge = highest_priority_tuples[-1]
        return bid, rule, hand_knowledge
