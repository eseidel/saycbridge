# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import os

from positionknowledge import PositionKnowledge
from core.suit import SUITS
from core.call import Call, Pass

from z3b.bidder import Interpreter, Bidder, InconsistentHistoryException
from z3b.model import positions
from z3b.preconditions import annotations
from z3b.forcing import SAYCForcingOracle


# FIXME: This is a horrible hack.  Callers should move off of the KBB HandConstraints API.
def _position_knowledge_from_position_view(position_view):
    kbb_constraints = PositionKnowledge()
    kbb_constraints.set_hcp_range(position_view.min_points, position_view.max_points)
    for suit in SUITS:
        kbb_constraints.set_length_range(suit, position_view.min_length(suit), position_view.max_length(suit))
    # FIXME: What about honor concentration?
    return kbb_constraints


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

        with Interpreter().extend_history(self.call_selection.rule_selector.history, self.call) as history:
            return _position_knowledge_from_position_view(history.rho)


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
        # kbb HandConstraints just so we can use it's pretty_print function.
        position_knowledge = _position_knowledge_from_position_view(position_view)
        kbb_oneline = position_knowledge.pretty_one_line(include_last_call_name=False)
        # FIXME: Annotation filtering belongs on the client, not here!
        annotations_whitelist = set([annotations.Artificial, annotations.NotrumpSystemsOn])
        annotations_for_last_call = set(position_view.annotations_for_last_call)#  & annotations_whitelist
        pretty_string = "%s %s" % (kbb_oneline, ", ".join(map(str, annotations_for_last_call)))
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
