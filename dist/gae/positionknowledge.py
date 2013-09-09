# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.suit import MINORS, SUITS


class HonorConstraint(object):
    UNKNOWN, FOURTH_ROUND_STOPPER, THIRD_ROUND_STOPPER, THREE_OF_TOP_FIVE, TWO_OF_TOP_THREE = range(5)

    @classmethod
    def short_name(cls, honor_constraint):
        return {
            cls.TWO_OF_TOP_THREE: '2o3',
            cls.THREE_OF_TOP_FIVE: '3o5',
            cls.THIRD_ROUND_STOPPER: '3rS',
            cls.FOURTH_ROUND_STOPPER: '4rS',
        }.get(honor_constraint)


class ControlConstraint(object):
    FIRST_ROUND, SECOND_ROUND = range(2)


class HandConstraints(object):
    MAX_HCP_PER_HAND = 37
    EMPTY_HCP_RANGE = (0, MAX_HCP_PER_HAND)
    ZERO_OR_FOUR = 5

    def __init__(self):
        self._hcp_range = self.EMPTY_HCP_RANGE
        self._suit_length_ranges = [(0, 13) for suit in SUITS]
        self._honors = [HonorConstraint.UNKNOWN for suit in SUITS]
        self._ace_constraint = None
        self._king_constraint = None
        self._longest_suit = None
        self._longest_suit_exceptions = ()
        self._longer_minor = None
        self._longer_major = None
        self._quick_tricks = None
        self._balanced = None
        self._controls = [[None for suit in SUITS], [None for suit in SUITS]]

    def _is_valid_range(self, tuple):
        min_value, max_value = tuple
        return min_value <= max_value

    # This is currently only used by the /explore UI for highlighting invalid bids.
    def is_valid(self):
        if not self._is_valid_range(self._hcp_range):
            return False
        for suit_range in self._suit_length_ranges:
            if not self._is_valid_range(suit_range):
                return False
        # FIXME: We could check other constraints here, like 3o5 requiring 3 cards in the suit, etc.
        return True

    def __str__(self):
        return self.pretty_one_line()

    def set_balanced(self):
        self._balanced = True
        # Note: This function is very hot.  We could probably save more time
        # by avoiding set_length_range calls in cases where they wouldn't do anthing.
        for suit in SUITS:
            # Balanced hands have at most one doubleton, and no more than 5 cards in a suit.
            self.set_length_range(suit, 2, 5, disable_implied_length_update=True)

    def is_balanced(self):
        return self._balanced

    def quick_tricks(self):
        return self._quick_tricks

    def set_quick_tricks(self, quick_tricks):
        self._quick_tricks = quick_tricks

    def longest_suit(self):
        return self._longest_suit

    def longest_suit_exceptions(self):
        return self._longest_suit_exceptions

    def set_longest_suit(self, suit, except_suits=None, disable_impled_length_update=None):
        self._longest_suit = suit
        self._longest_suit_exceptions = except_suits or ()
        self.set_min_length(suit, 4)

    def longer_minor(self):
        return self._longer_minor

    def set_longer_minor(self, suit, disable_impled_length_update=None):
        self._longer_minor = suit

    def longer_major(self):
        return self._longer_major

    def set_longer_major(self, suit, disable_impled_length_update=None):
        self._longer_major = suit

    def _range_from_tuple(self, range_tuple):
        return range(range_tuple[0], range_tuple[1] + 1)

    def _updated_range_tuple(self, old_tuple, new_min, new_max):
        old_min, old_max = old_tuple
        return (max(new_min, old_min), min(new_max, old_max))

    # FIXME: This name is slightly misleading, since we are actually just restricting the range.
    def set_hcp_range(self, min_hcp, max_hcp):
        self._hcp_range = self._updated_range_tuple(self._hcp_range, min_hcp, max_hcp)

    def min_hcp(self):
        return self._hcp_range[0]

    def max_hcp(self):
        return self._hcp_range[1]

    def set_min_hcp(self, min_hcp):
        self.set_hcp_range(min_hcp, self.MAX_HCP_PER_HAND)

    def set_max_hcp(self, max_hcp):
        self.set_hcp_range(0, max_hcp)

    # Note: If ace_constraint == ZERO_OR_FOUR, that means "zero or four" aces. Shoot me now.
    def set_ace_constraint(self, ace_constraint):
        self._ace_constraint = ace_constraint

    # Note: If ace_constraint == ZERO_OR_FOUR, that means "zero or four" aces. Shoot me now.
    def ace_constraint(self):
        return self._ace_constraint

    # Note: If king_constraint == ZERO_OR_FOUR, that means "zero or four" kings. Shoot me now.
    def set_king_constraint(self, king_constraint):
        self._king_constraint = king_constraint

    # Note: If king_constraint == ZERO_OR_FOUR, that means "zero or four" kings. Shoot me now.
    def king_constraint(self):
        return self._king_constraint

    def set_control_for_round(self, suit, control_round, have_control):
        self._controls[control_round][suit.index] = have_control

    def control_for_round(self, suit, control_round):
        return self._controls[control_round][suit.index]

    def set_min_honors(self, suit, honor_constraint):
        self._honors[suit.index] = max(honor_constraint, self._honors[suit.index])

    def min_honors(self, suit):
        return self._honors[suit.index]

    def length_range(self, suit):
        return self._range_from_tuple(self._suit_length_ranges[suit.index])

    def set_length_range(self, suit, min_length, max_length, disable_implied_length_update=None):
        assert suit in SUITS, "%s is not a suit!" % suit
        previous_length_range = self._suit_length_ranges[suit.index]
        self._suit_length_ranges[suit.index] = self._updated_range_tuple(self._suit_length_ranges[suit.index], min_length, max_length)

    def set_length(self, suit, length, disable_implied_length_update=None):
        self.set_length_range(suit, length, length, disable_implied_length_update=disable_implied_length_update)

    def min_length(self, suit):
        return self._suit_length_ranges[suit.index][0]

    def set_min_length(self, suit, min_length, disable_implied_length_update=None):
        self.set_length_range(suit, min_length, 13, disable_implied_length_update=disable_implied_length_update)

    def max_length(self, suit):
        return self._suit_length_ranges[suit.index][1]

    def set_max_length(self, suit, max_length, disable_implied_length_update=None):
        self.set_length_range(suit, 0, max_length, disable_implied_length_update=disable_implied_length_update)

    def _string_for_range(self, range_tuple, global_max=None):
        # This len check only exists for trying to print invalid hand constraints.
        min_value, max_value = range_tuple
        if min_value == max_value:
            return str(min_value)
        if min_value == 0 and max_value >= global_max:
            return "?"  # To indicate no information.
        if max_value >= global_max:
            return "%s+" % min_value
        # Could use <5 syntax, but that looks strange for suit lengths.
        # if min_value == 0:
        #     return "<%s" % max_value
        return "%s-%s" % (min_value, max_value)

    def _pretty_string_for_suit(self, suit, max_suit_length_to_show=None):
        max_suit_length_to_show = max_suit_length_to_show or 6
        suit_string = self._string_for_range(self._suit_length_ranges[suit.index], global_max=max_suit_length_to_show)
        suit_options = []
        if self.min_honors(suit):
            suit_options.append(HonorConstraint.short_name(self.min_honors(suit)))
        first_round_control = self.control_for_round(suit, ControlConstraint.FIRST_ROUND)
        if first_round_control is not None:
            if first_round_control:
                suit_options.append("1rC")
            else:
                suit_options.append("!1rC")
        second_round_control = self.control_for_round(suit, ControlConstraint.SECOND_ROUND)
        if second_round_control is not None:
            if second_round_control:
                suit_options.append("2rC")
            else:
                suit_options.append("!2rC")
        if suit_string == "?" and not suit_options:
            return None
        suit_string += suit.char
        if suit_options:
            suit_string += "(%s)" % (", ".join(suit_options))
        return suit_string

    def pretty_one_line(self):
        # Building the strings for the empty constraints is needlessly expensive (also a single ? looks better).
        if self._hcp_range == self.EMPTY_HCP_RANGE and self._suit_length_ranges.count((0, 13)) == 4 and self._honors.count(HonorConstraint.UNKNOWN) == 4:
            return "?"
        suit_strings = [self._pretty_string_for_suit(suit) for suit in SUITS]
        # Don't bother to show suits we know nothing about.
        suit_strings = filter(lambda string: bool(string), suit_strings)
        pretty_string = "%s hcp" % self._string_for_range(self._hcp_range, global_max=self.MAX_HCP_PER_HAND)
        if suit_strings:
            return "%s, %s" % (pretty_string, " ".join(suit_strings))
        return pretty_string


# FIXME: Merge with HandConstraints.
class PositionKnowledge(HandConstraints):
    def __init__(self):
        HandConstraints.__init__(self)
        self.last_call = None
        self.opened = False
        self.notrump_protocol = False
        self.rule_of_twenty = None
        self.rule_of_fifteen = None

    def explore_string(self):
        return self.pretty_one_line(include_last_call_name=False)

    def pretty_one_line(self, include_last_call_name=True):
        pretty_line = HandConstraints.pretty_one_line(self)
        if self.last_call or self.opened:
            info_strings = []
            if include_last_call_name:
                info_strings.append("last: %s" % self.last_call)
            else:
                last_call_string = self.last_call.pretty_one_line(include_bid_name=False)
                if last_call_string:
                    info_strings.append(last_call_string)
            if self.opened:
                info_strings.append("opened")
            if self.notrump_protocol:
                info_strings.append("nt")
            if self.ace_constraint() is not None:
                ace_constraint = self.ace_constraint()
                ace_count = "0 or 4" if ace_constraint == HandConstraints.ZERO_OR_FOUR else str(ace_constraint)
                info_strings.append("aces(%s)" % ace_count)
            if self.king_constraint() is not None:
                king_constraint = self.king_constraint()
                king_count = "0 or 4" if king_constraint == HandConstraints.ZERO_OR_FOUR else str(king_constraint)
                info_strings.append("kings(%s)" % king_count)
            if info_strings:
                pretty_line +=" (%s)" % ", ".join(info_strings)
        return pretty_line
