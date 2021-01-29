# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import os

from core.suit import SUITS
from core.call import Call, Pass


class ConstraintsSerializer(object):
    MAX_HCP_PER_HAND = 37
    EMPTY_HCP_RANGE = (0, MAX_HCP_PER_HAND)

    def __init__(self, position_view):
        self._hcp_range = (position_view.min_points, position_view.max_points)
        self._suit_length_ranges = [(position_view.min_length(suit), position_view.max_length(suit)) for suit in SUITS]

    def _string_for_range(self, range_tuple, global_max):
        # This len check only exists for trying to print invalid hand constraints.
        min_value, max_value = range_tuple
        if min_value == max_value:
            return str(min_value)
        if min_value == 0 and max_value >= global_max:
            return "?"  # To indicate no information.
        if max_value >= global_max:
            return "%s+" % min_value
        return "%s-%s" % (min_value, max_value)

    def _pretty_string_for_suit(self, suit, max_suit_length_to_show=None):
        max_suit_length_to_show = max_suit_length_to_show or 6
        suit_string = self._string_for_range(self._suit_length_ranges[suit.index], max_suit_length_to_show)
        if suit_string == "?":
            return None
        return suit_string + suit.char

    def explore_string(self):
        # Building the strings for the empty constraints is needlessly expensive (also a single ? looks better).
        if self._hcp_range == self.EMPTY_HCP_RANGE and self._suit_length_ranges.count((0, 13)) == 4:
            return "?"
        suit_strings = [self._pretty_string_for_suit(suit) for suit in SUITS]
        # Don't bother to show suits we know nothing about.
        suit_strings = filter(lambda string: bool(string), suit_strings)
        pretty_string = "%s hcp" % self._string_for_range(self._hcp_range, self.MAX_HCP_PER_HAND)
        if suit_strings:
            return "%s, %s" % (pretty_string, " ".join(suit_strings))
        return pretty_string

