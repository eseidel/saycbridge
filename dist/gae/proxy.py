# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import os

from core.suit import SUITS
from core.call import Call, Pass

from z3b.bidder import Interpreter, Bidder, InconsistentHistoryException
from z3b.model import positions
from z3b.preconditions import annotations
from z3b.forcing import SAYCForcingOracle


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


# FIXME: This is a hack to make the GAE front-end work with the Z3 Bidder.
class CallSelectionProxy(object):
    def __init__(self, call_selection):
        self.call = call_selection.call if call_selection else None
        self.rule = call_selection.rule if call_selection else None
        self.call_selection = call_selection

    @property
    def hand_knowledge(self):
        if not self.call:
            return None

        try:
            with Interpreter().extend_history(self.call_selection.rule_selector.history, self.call) as history:
                return ConstraintsSerializer(history.rho)
        except InconsistentHistoryException:
            return None


class BidderProxy(object):
    def __init__(self):
        self.bidder = Bidder()

    def find_call_for(self, hand, call_history):
        return self.bidder.find_call_for(hand, call_history)

    def call_selection_for(self, hand, call_history):
        return CallSelectionProxy(self.bidder.call_selection_for(hand, call_history))


# This is used by the explorer (explorer_handler.py)
class InterpreterProxy(object):
    def __init__(self):
        self.interpreter = Interpreter()

    def _pretty_string_for_position_view(self, position_view):
        explore_string = ConstraintsSerializer(position_view).explore_string()
        # FIXME: Annotation filtering belongs on the client, not here!
        annotations_whitelist = set([annotations.Artificial, annotations.NotrumpSystemsOn])
        annotations_for_last_call = set(position_view.annotations_for_last_call) & annotations_whitelist
        pretty_string = "%s %s" % (explore_string, ", ".join(map(str, annotations_for_last_call)))
        # Only bother trying to interpret if the bid is forcing if we understood it in the first place:
        if position_view.rule_for_last_call:
            try:
                partner_future = self.interpreter.extend_history(position_view.history, Pass())
                if SAYCForcingOracle().forced_to_bid(partner_future):
                    pretty_string += " Forcing"
            except InconsistentHistoryException:
                pass
        return pretty_string

    def knowledge_string_and_rule_for_additional_call(self, history, call):
        try:
            history = self.interpreter.extend_history(history, call)
            return self._pretty_string_for_position_view(history.rho), history.rho.rule_for_last_call
        except InconsistentHistoryException, e:
            return None, None

    def knowledge_string_and_rule_for_last_call(self, call_history):
        with self.interpreter.create_history(call_history) as history:
            return self._pretty_string_for_position_view(history.rho), history.rho.rule_for_last_call

    def create_history(self, call_history):
        return self.interpreter.create_history(call_history)
