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
from kbb.handconstraints import HandConstraints
from core.suit import SUITS


class BidderProxy(object):
    def __init__(self):
        if use_z3:
            # We can't import Z3 in GAE.
            from z3b.bidder import Bidder
            self.bidder = Bidder()
        else:
            self.bidder = KnowledgeBasedBidder()

    def find_call_for(self, hand, call_history):
        return self.bidder.find_call_for(hand, call_history)

    def find_call_and_rule_and_hand_knowledge_for(self, hand, call_history):
        # FIXME: This is a hack to make the GAE front-end work with the Z3 Bidder.
        if use_z3:
            call_and_rule = self.bidder.find_call_and_rule_for(hand, call_history)
            return [call_and_rule[0], call_and_rule[1], None]
        return self.bidder.find_call_and_rule_and_hand_knowledge_for(hand, call_history)


# This is used by the explorer (explorer_handler.py)
# The Explorer doesn't actually work for z3 yet, but this
# documents what interface we'd have to provide to make it work.
class InterpreterProxy(object):
    def __init__(self):
        if use_z3:
            from z3b.bidder import Interpreter
            self.interpreter = Interpreter()
        else:
            self.interpreter = BidInterpreter()

    def _pretty_string_for_history(self, history, position):
        from z3b.model import positions
        # FIXME: This is a horrible hack where we map z3 knowledge into
        # kbb HandConstraints just so we can use it's pretty_print function.
        kbb_constraints = HandConstraints()
        kbb_constraints.set_min_hcp(history.rho.min_points)
        # FIXME: What about max_hcp?
        for suit in SUITS:
            kbb_constraints.set_min_length(suit, history.rho.min_length(suit))
        # FIXME: What about max_length?
        # FIXME: What about honor concentration?

        kbb_oneline = kbb_constraints.pretty_one_line()
        annotations = history.annotations_for_last_call(positions.RHO)
        return kbb_oneline + " " + ", ".join(map(str, annotations))

    def knowledge_string_and_rule_for_last_call(self, call_history):
        knowledge_string = None
        rule = None
        if use_z3:
            from z3b.model import positions
            with self.interpreter.create_history(call_history) as history:
                return self._pretty_string_for_history(history, positions.RHO), history.rule_for_last_call(positions.RHO)
        else:
            existing_knowledge, knowledge_builder = self.interpreter.knowledge_from_history(call_history)
            matched_rules = knowledge_builder.matched_rules()
            knowledge_string = existing_knowledge.rho.pretty_one_line(include_last_call_name=False) if existing_knowledge else None,
            return knowledge_string, matched_rules[-1]

    def knowledge_from_history(self, call_history, loose_constraints=None):
        if use_z3:
            return (None, None)
        return self.interpreter.knowledge_from_history(call_history, loose_constraints)

