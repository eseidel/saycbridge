# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import os

# The Z3 Bidder and the KBB do not quite have the same interface.
# Yet we'd like to continue letting both work with the GAE interface for now.
# This module detects which we should use, and proxies KBB-style calls to the Z3 Bidder.
# This module is the *ONLY* place in GAE which should know about the two bidders.

# This is our hackish way of detecting app-engine vs. Werkzeug (our current z3 server harness)
use_z3 = not os.environ.get('SERVER_SOFTWARE')

from kbb.bidder import KnowledgeBasedBidder
from kbb.interpreter import BidInterpreter
from kbb.knowledge import PositionKnowledge
from core.suit import SUITS
import core.call

# We can't import z3 in GAE.
if use_z3:
    from z3b.bidder import Interpreter, Bidder, InconsistentHistoryException
    from z3b.model import positions


# FIXME: This is a horrible hack.  Callers should move off of the KBB HandConstraints API.
def _position_knowledge_from_position_view(position_view):
    kbb_constraints = PositionKnowledge()
    kbb_constraints.set_hcp_range(position_view.min_points, position_view.max_points)
    for suit in SUITS:
        kbb_constraints.set_length_range(suit, position_view.min_length(suit), position_view.max_length(suit))
    # FIXME: What about honor concentration?
    return kbb_constraints

class BidderProxy(object):
    def __init__(self):
        if use_z3:
            self.bidder = Bidder()
        else:
            self.bidder = KnowledgeBasedBidder()

    def find_call_for(self, hand, call_history):
        return self.bidder.find_call_for(hand, call_history)

    def find_call_and_rule_and_hand_knowledge_for(self, hand, call_history):
        # FIXME: This is a hack to make the GAE front-end work with the Z3 Bidder.
        if use_z3:
            call = self.bidder.find_call_for(hand, call_history)
            new_call_history = call_history.copy_appending_call(call if call else core.call.Pass())
            # FIXME: Figure out the clean way to have the Bidder return the updated History
            # instead of interpreting the whole call history twice!
            with Interpreter().create_history(new_call_history) as history:
                return [call, history.rho.rule_for_last_call, _position_knowledge_from_position_view(history.rho)]
        return self.bidder.find_call_and_rule_and_hand_knowledge_for(hand, call_history)


# This is used by the explorer (explorer_handler.py)
class InterpreterProxy(object):
    def __init__(self):
        if use_z3:
            self.interpreter = Interpreter()
        else:
            self.interpreter = BidInterpreter()

    def _pretty_string_for_position_view(self, position_view):
        # kbb HandConstraints just so we can use it's pretty_print function.
        position_knowledge = _position_knowledge_from_position_view(position_view)
        kbb_oneline = position_knowledge.pretty_one_line(include_last_call_name=False)
        return kbb_oneline + " " + ", ".join(map(str, position_view.annotations_for_last_call))

    def knowledge_string_and_rule_for_additional_call(self, history, call):
        knowledge_string = None
        rule = None
        if not use_z3:
            raise NotImplementedError
        try:
            history = self.interpreter.extend_history(history, call)
            return self._pretty_string_for_position_view(history.rho), history.rho.rule_for_last_call
        except InconsistentHistoryException, e:
            return None, None

    def knowledge_string_and_rule_for_last_call(self, call_history):
        knowledge_string = None
        rule = None
        if use_z3:
            with self.interpreter.create_history(call_history) as history:
                return self._pretty_string_for_position_view(history.rho), history.rho.rule_for_last_call
        else:
            existing_knowledge, knowledge_builder = self.interpreter.knowledge_from_history(call_history)
            matched_rules = knowledge_builder.matched_rules()
            knowledge_string = existing_knowledge.rho.pretty_one_line(include_last_call_name=False) if existing_knowledge else None,
            return knowledge_string, matched_rules[-1]

    def create_history(self, call_history):
        return self.interpreter.create_history(call_history)
