from core.suit import *
from kbb.handconstraints import HonorConstraint, ControlConstraint

import logging
_log = logging.getLogger(__name__)


class Constraint(object):
    def apply_to(self, knowledge, bid):
        pass


# WARNING! This constraint is extremely powerful and should be used with caution!
class ForgetEverythingAboutMe(Constraint):
    def apply_to(self, knowledge, bid):
        knowledge.me.forget_everything()


class HighCardPointRange(Constraint):
    def __init__(self, min_hcp, max_hcp):
        self.min_hcp = min_hcp
        self.max_hcp = max_hcp

    def apply_to(self, knowledge, bid):
        knowledge.me.set_hcp_range(self.min_hcp, self.max_hcp)


class MaxHighCardPoints(Constraint):
    def __init__(self, max_hcp):
        self.max_hcp = max_hcp

    def apply_to(self, knowledge, bid):
        knowledge.me.set_max_hcp(self.max_hcp)


class MinHighCardPoints(Constraint):
    def __init__(self, min_hcp):
        self.min_hcp = min_hcp

    def apply_to(self, knowledge, bid):
        knowledge.me.set_min_hcp(self.min_hcp)


class Aces(Constraint):
    def __init__(self, constraint):
        self._constraint = constraint

    def apply_to(self, knowledge, bid):
        knowledge.me.set_ace_constraint(self._constraint)


class Kings(Constraint):
    def __init__(self, constraint):
        self._constraint = constraint

    def apply_to(self, knowledge, bid):
        knowledge.me.set_king_constraint(self._constraint)


class MinHonors(Constraint):
    def __init__(self, honor_constraint, suit=None):
        self._suit = suit
        self._honor_constraint = honor_constraint

    def apply_to(self, knowledge, bid):
        suit = bid.strain if self._suit is None else self._suit
        knowledge.me.set_min_honors(suit, self._honor_constraint)


class Control(Constraint):
    def __init__(self, suit=None):
        self._suit = suit

    @classmethod
    def _is_control_known(self, knowledge, suit):
        return (knowledge.partner.control_for_round(suit, ControlConstraint.FIRST_ROUND) is not None
            or knowledge.me.control_for_round(suit, ControlConstraint.FIRST_ROUND) is not None)

    def apply_to(self, knowledge, bid):
        suit = bid.strain if self._suit is None else self._suit
        if Control._is_control_known(knowledge, suit):
            control_round = ControlConstraint.SECOND_ROUND
        else:
            control_round = ControlConstraint.FIRST_ROUND

        knowledge.me.set_control_for_round(suit, control_round, True)


class NoControlInSkippedSuits(Constraint):
    def _have_fit(self, knowledge, suit):
        return (knowledge.me.min_length(suit) + knowledge.partner.min_length(suit)) >= 8

    def apply_to(self, knowledge, bid):
        last_suit = knowledge.last_contract().strain
        bid_suit = bid.strain
        skip_offset = (bid_suit - last_suit - 1) % 4
        for suit_offset in range(skip_offset):
            skipped_suit = (last_suit + suit_offset + 1) % 4

            # Skipping trump does not indicate lack of controls.
            # FIXME: This will behave wrong if we've identified two fits!
            if self._have_fit(knowledge, skipped_suit):
                continue

            if Control._is_control_known(knowledge, skipped_suit):
                control_round = ControlConstraint.SECOND_ROUND
            else:
                control_round = ControlConstraint.FIRST_ROUND
            knowledge.me.set_control_for_round(skipped_suit, control_round, False)


class Balanced(Constraint):
    def apply_to(self, knowledge, bid):
        assert bid.is_double() or bid.strain == NOTRUMP  # I know of no way in SAYC to show a balanced hand besides a NT bid or X.
        knowledge.me.set_balanced()


class LongestSuit(Constraint):
    def apply_to(self, knowledge, bid):
        assert bid.strain in SUITS
        knowledge.me.set_longest_suit(bid.strain)


class LongestSuitExceptOpponentSuits(Constraint):
    def apply_to(self, knowledge, bid):
        knowledge.me.set_longest_suit(bid.strain, except_suits=knowledge.their_bid_suits())


class LongerMajor(Constraint):
    def apply_to(self, knowledge, bid):
        assert bid.strain in MAJORS
        knowledge.me.set_longer_major(bid.strain)


class LongerMinor(Constraint):
    def apply_to(self, knowledge, bid):
        assert bid.strain in MINORS
        knowledge.me.set_longer_minor(bid.strain)


class LongestMinorOrMajorIsNowLongestSuit(Constraint):
    def apply_to(self, knowledge, bid):
        assert (knowledge.me.longer_major() is None) != (knowledge.me.longer_minor() is None)
        if knowledge.me.longer_major() is not None:
            longest_suit = knowledge.me.longer_major()
        else:
            longest_suit = knowledge.me.longer_minor()
        knowledge.me.set_longest_suit(longest_suit)


class NoSecondFiveCardSuit(Constraint):
    def apply_to(self, knowledge, bid):
        longest_suit = knowledge.me.longest_suit()
        assert longest_suit is not None
        for suit in SUITS:
            if suit != longest_suit:
                knowledge.me.set_max_length(suit, 4)


class StopperInRHOSuit(Constraint):
    def apply_to(self, knowledge, bid):
        rho_suit = knowledge.rho.last_call.strain
        if not rho_suit:
            return
        knowledge.me.set_min_honors(rho_suit, HonorConstraint.FOURTH_ROUND_STOPPER)


class StopperInFourthSuit(Constraint):
    def apply_to(self, knowledge, bid):
        partner_last_call = knowledge.partner.last_call
        assert partner_last_call.fourth_suit_forcing
        knowledge.me.set_min_honors(partner_last_call.strain, HonorConstraint.FOURTH_ROUND_STOPPER)


class StoppersInUnbidSuits(Constraint):
    def apply_to(self, knowledge, bid):
        # If partner opened NT, we don't need to check for stoppers, right?
        if knowledge.partner.opened and knowledge.partner.is_balanced() and knowledge.partner.min_hcp() >= 15:
            return

        # If we opened NT, we don't need to check for stoppers, right?
        if knowledge.me.opened and knowledge.me.is_balanced() and knowledge.me.min_hcp() >= 15:
            return

        for suit in SUITS:
            # FIXME: Ideally this would be >= 4, except then it wouldn't count a minor opening as a stopper
            # even though we probably should.  Maybe we can cover those with a "longest suit" logic rule
            # and restore this to >= 4 in a suit?
            if knowledge.partner.min_honors(suit) >= HonorConstraint.FOURTH_ROUND_STOPPER:
                continue  # Partner has already shown a stopper.
            if knowledge.partner.did_bid_suit(suit):
                continue  # Partner must have "bid" this suit, which we'll count as a stopper.
            if knowledge.me.did_bid_suit(suit):
                continue  # I must have "bid" this suit.
            knowledge.me.set_min_honors(suit, HonorConstraint.FOURTH_ROUND_STOPPER)


# FIXME: This should share more code with StoppersInUnbidSuits.
class StoppersInOpponentsSuits(Constraint):
    def _is_natural_suit(self, bid, suit):
        return bid and bid.strain == suit and not bid.artificial

    def _is_stopper_needed(self, knowledge, suit):
        assert suit in SUITS
        # FIXME: This will not count unsupported 1-level overcalls as "bid".
        if knowledge.rho.min_length(suit) + knowledge.lho.min_length(suit) >= 5:
            return True
        if self._is_natural_suit(knowledge.rho.last_call, suit):
            return True
        if self._is_natural_suit(knowledge.lho.last_call, suit):
            return True
        return False

    def apply_to(self, knowledge, bid):
        # If partner opened NT, we don't need to check for stoppers, right?
        if knowledge.partner.opened and knowledge.partner.is_balanced() and knowledge.partner.min_hcp() >= 15:
            return

        # If partner bid a natural NT, we don't need to check for stoppers, right?
        # FIXME: We probably still need a stopper in RHO's suit if it was a new suit!
        if knowledge.partner.last_call and knowledge.partner.last_call.strain == NOTRUMP and knowledge.partner.is_balanced():
            return

        for suit in [suit for suit in SUITS if self._is_stopper_needed(knowledge, suit)]:
            # If partner has already shown a stopper, we don't need to.
            if knowledge.partner.min_honors(suit) >= HonorConstraint.FOURTH_ROUND_STOPPER:
                continue
            knowledge.me.set_min_honors(suit, HonorConstraint.FOURTH_ROUND_STOPPER)


class RuleOfTwenty(Constraint):
    def __init__(self, matches_rule=None):
        self.matches_rule = matches_rule
        if self.matches_rule is None:
            self.matches_rule = True

    def apply_to(self, knowledge, bid):
        knowledge.me.rule_of_twenty = self.matches_rule
        # FIXME: This should also set min_hcp=12.


class RuleOfFifteen(Constraint):
    def __init__(self, matches_rule=None):
        self.matches_rule = matches_rule
        if self.matches_rule is None:
            self.matches_rule = True

    def apply_to(self, knowledge, bid):
        knowledge.me.rule_of_fifteen = self.matches_rule


class CouldBeStrongFourCardSuit(Constraint):
    def apply_to(self, knowledge, bid):
        assert bid.strain in SUITS
        knowledge.me.set_could_be_strong_four_card(bid.strain)


class MinLength(Constraint):
    def __init__(self, min_length, suit=None):
        self.suit = suit
        self.min_length = min_length

    def apply_to(self, knowledge, bid):
        suit = bid.strain if self.suit is None else self.suit
        knowledge.me.set_min_length(suit, self.min_length)


class MaxLength(Constraint):
    def __init__(self, max_length, suit=None):
        self.suit = suit
        self.max_length = max_length

    def apply_to(self, knowledge, bid):
        suit = bid.strain if self.suit is None else self.suit
        knowledge.me.set_max_length(suit, self.max_length)


class Length(Constraint):
    def __init__(self, length, suit=None):
        self.suit = suit
        self.length = length

    def apply_to(self, knowledge, bid):
        suit = bid.strain if self.suit is None else self.suit
        knowledge.me.set_length(suit, self.length)


class SetOpened(Constraint):
    def apply_to(self, knowledge, bid):
        knowledge.me.opened = True


# Some NT bids put the auction into a "notrump" state where the bidding rules
# change. For example, notrump systems can be on and the suit introduction
# rules from suited auctions no longer apply.
class SetNotrumpProtocol(Constraint):
    def apply_to(self, knowledge, bid):
        knowledge.me.notrump_protocol = True


class NoFit(Constraint):
    def apply_to(self, knowledge, bid):
        for suit in SUITS:
            partner_promised_length = knowledge.partner.min_length(suit)
            knowledge.me.set_max_length(suit, 8 - partner_promised_length - 1)


class NoMajorFit(Constraint):
    def apply_to(self, knowledge, bid):
        for suit in MAJORS:
            partner_promised_length = knowledge.partner.min_length(suit)
            knowledge.me.set_max_length(suit, 8 - partner_promised_length - 1)


class MinimumCombinedLength(Constraint):
    def __init__(self, min_count, suit=None, use_last_call_suit=None):
        self.min_count = min_count
        self.suit = suit
        self.use_last_call_suit = use_last_call_suit or False

    def _effective_suit(self, knowledge, bid):
        if self.use_last_call_suit:
            return knowledge.last_contract().strain
        return bid.strain if self.suit is None else self.suit

    def apply_to(self, knowledge, bid):
        suit = self._effective_suit(knowledge, bid)
        partner_promised_length = knowledge.partner.min_length(suit)
        implied_length = max(self.min_count - partner_promised_length, 0)
        knowledge.me.set_min_length(suit, implied_length)


class BetterFitThanPartnerLastContract(Constraint):
    def apply_to(self, knowledge, bid):
        last_suit = knowledge.partner.last_call.strain
        if last_suit == NOTRUMP:
            # If partner's last bid was NT, then a better fit is a real fit?
            combined_min_in_last_suit = 8
        else:
            assert last_suit in SUITS
            partner_min_in_last_suit = knowledge.partner.min_length(last_suit)
            combined_min_in_last_suit = partner_min_in_last_suit + knowledge.me.min_length(last_suit)

        suit = bid.strain
        partner_min_in_this_suit = knowledge.partner.min_length(suit)
        implied_min_in_this_suit = max(combined_min_in_last_suit - partner_min_in_this_suit + 1, 0)
        # FIXME: Alternatively we could have better honor concentration in this suit?
        knowledge.me.set_min_length(suit, implied_min_in_this_suit)

        # FIXME: We're also denying a fit with partner's suit?
        # implied_max_in_this_suit = max(7 - partner_min_in_last_suit, 0)
        # knowledge.me.set_max_length(last_suit, implied_max_in_this_suit)


class LengthSatisfiesLawOfTotalTricks(Constraint):
    def apply_to(self, knowledge, bid):
        # Written forward: level = partner_min + my_min - 6
        my_count = bid.level() + 6 - knowledge.partner.min_length(bid.strain)
        knowledge.me.set_min_length(bid.strain, my_count)


class MinimumCombinedPoints(Constraint):
    def __init__(self, min_points):
        self.min_points = min_points

    def apply_to(self, knowledge, bid):
        implied_points = max(0, self.min_points - knowledge.partner.min_hcp())
        knowledge.me.set_min_hcp(implied_points)


class MaximumCombinedPoints(Constraint):
    def __init__(self, max_points):
        self.max_points = max_points

    def apply_to(self, knowledge, bid):
        implied_points = max(0, self.max_points - knowledge.partner.max_hcp())
        knowledge.me.set_max_hcp(implied_points)


class CombinedPointRangeOverPartnerMinimum(Constraint):
    def __init__(self, min_combined_points, max_combined_points):
        self.min_combined_points = min_combined_points
        self.max_combined_points = max_combined_points

    def apply_to(self, knowledge, bid):
        partner_min_points = knowledge.partner.min_hcp()
        implied_min_points = max(0, self.min_combined_points - partner_min_points)
        implied_max_points = max(0, self.max_combined_points - partner_min_points)
        knowledge.me.set_hcp_range(implied_min_points, implied_max_points)


class NoAvailableFourCardSuit(Constraint):
    def apply_to(self, knowledge, bid):
        last_contract = knowledge.last_contract()
        assert last_contract and last_contract.strain is not None
        for skipped_suit in range(last_contract.strain + 1, SPADES + 1):
            knowledge.me.set_max_length(skipped_suit, 3)


class NoAvailableNonReverse(Constraint):
    def apply_to(self, knowledge, bid):
        last_call = knowledge.me.last_call
        assert last_call and last_call.strain is not None
        for skipped_suit in range(CLUBS, last_call.strain):
            knowledge.me.set_max_length(skipped_suit, 3)


class MaxLengthForAnySuit(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def apply_to(self, knowledge, bid):
        for suit in SUITS:
            knowledge.me.set_max_length(suit, self.max_length)


class NoAvailableFourCardMajor(Constraint):
    def apply_to(self, knowledge, bid):
        last_contract = knowledge.last_contract()
        assert last_contract and last_contract.strain is not None
        for skipped_suit in range(max(last_contract.strain + 1, HEARTS), SPADES + 1):
            knowledge.me.set_max_length(skipped_suit, 3)


class LessThanFourCardsInAllSkippedSuits(Constraint):
    def _skipped_suits(self, knowledge, bid):
        last_contract = knowledge.last_contract()
        if bid.level() > last_contract.level() and bid.strain >= last_contract.strain:
            return knowledge.unbid_suits()  # If we jumped, then we skipped all the suits!

        last_suit = last_contract.strain
        assert last_suit is not None
        if last_suit == NOTRUMP:
            last_suit = SPADES  # This keeps the skip_offset consistent.

        bid_suit = bid.strain
        skip_offset = (bid_suit - last_suit - 1) % 4

        return [(last_suit + suit_offset + 1) % 4 for suit_offset in range(skip_offset)]

    def apply_to(self, knowledge, bid):
        for skipped_suit in self._skipped_suits(knowledge, bid):
            # We're only denying a suit if we've said nothing about it before.
            # FIXME: This min_length == 0 check makes applying this constraint order-sensitive!
            if knowledge.me.min_length(skipped_suit) == 0:
                knowledge.me.set_max_length(skipped_suit, 3)


class SupportForPartnerLastBid(Constraint):
    def __init__(self, min_count):
        self._min_count = min_count

    def apply_to(self, knowledge, bid):
        partner_suit = knowledge.partner.last_call.strain
        knowledge.me.set_min_length(partner_suit, self._min_count)


class MaximumLengthInOtherMajor(Constraint):
    def __init__(self, max_count):
        self._max_count = max_count

    def apply_to(self, knowledge, bid):
        partner_suit = knowledge.partner.last_call.strain
        assert partner_suit in MAJORS
        assert not knowledge.partner.last_call.artificial
        knowledge.me.set_max_length(other_major(partner_suit), self._max_count)


class MaximumLengthInSuitsOtherThanMyLast(Constraint):
    def __init__(self, max_count):
        self._max_count = max_count

    def apply_to(self, knowledge, bid):
        for suit in SUITS:
            if suit == knowledge.me.last_call.strain:
                continue
            knowledge.me.set_max_length(suit, self._max_count)


class LengthInOtherMajor(Constraint):
    def __init__(self, count):
        self._count = count

    def apply_to(self, knowledge, bid):
        partner_suit = knowledge.partner.last_call.strain
        if partner_suit not in MAJORS:
            return
        knowledge.me.set_length(other_major(partner_suit), self._count)


class MaximumLengthInLastBidSuit(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def apply_to(self, knowledge, bid):
        knowledge.me.set_max_length(knowledge.last_contract().strain, self.max_length)


class MaximumLengthInOpponentsSuits(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def apply_to(self, knowledge, bid):
        for suit in knowledge.their_bid_suits():
            knowledge.me.set_max_length(suit, self.max_length)


class MaximumLengthInPartnerLastBidSuit(Constraint):
    def __init__(self, max_length):
        self.max_length = max_length

    def apply_to(self, knowledge, bid):
        partner_suit = knowledge.partner.last_call.strain
        assert not knowledge.partner.last_call.artificial
        knowledge.me.set_max_length(partner_suit, self.max_length)


class MinimumLengthInSuitsOtherThanLastBidSuit(Constraint):
    def __init__(self, min_length):
        self.min_length = min_length

    def apply_to(self, knowledge, bid):
        last_suit = knowledge.last_contract().strain
        assert last_suit in SUITS
        for suit in SUITS:
            if suit != last_suit:
                knowledge.me.set_min_length(suit, self.min_length)


class SupportForUnbidSuits(Constraint):
    def apply_to(self, knowledge, bid):
        unbid_suits = knowledge.unbid_suits()

        # If there are only 2 unbid suits, we should have at least 4 in each to be takeout doubling.
        # We'd like to make this ASSERT, but we hit it too often when people make invalid bids
        # which we don't understand as artificial (or natural for that matter)
        # thus don't realize if they've shown a suit.  2C P 3S is an example of where considering X would assert here.
        # assert len(unbid_suits) in (2, 3), "Unexpected number of unbid suits: %s" % len(unbid_suits)
        if len(unbid_suits) == 2:
            min_length = 4
        else:
            min_length = 3

        for suit in unbid_suits:
            knowledge.me.set_min_length(suit, min_length)


class MinCombinedPointsForPartnerMinimumRebid(Constraint):
    def _min_points_for_cheapest_notrump(self, level):
        return {
            1: 19,
            2: 22,
            3: 25,
            4: 28,
            5: 30,
            6: 33,
            7: 37,
        }[level]

    def apply_to(self, knowledge, call):
        # Natural NT bids are never forcing.  So we don't promise extra points for partner.
        # No way to test natural from "bid" yet.
        if call.strain == NOTRUMP:
            return

        # If we're forcing partner to bid, we're promising it's OK to escape to NT with a minimum.
        level = call.level() if call.level() else knowledge.last_contract().level()
        knowledge.me.set_min_hcp(self._min_points_for_cheapest_notrump(level) - knowledge.partner.min_hcp())
        # FIXME: It's possible that partner doesn't need quite points for cheapest NT, if
        # a suit rebid is available (and could be made with a couple fewer points).
