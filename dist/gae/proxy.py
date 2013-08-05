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
            self.interpreter = None
        else:
            self.interpreter = BidInterpreter()

    def knowledge_from_history(self, call_history, loose_constraints=None):
        if use_z3:
            return (None, None)
        return self.interpreter.knowledge_from_history(call_history, loose_constraints)

    def knowledge_including_new_bid(self, knowledge_builder, new_bid, convention_card=None, loose_constraints=None):
        if use_z3:
            return (None, None)
        return self.interpreter.knowledge_including_new_bid(knowledge_builder, new_bid, convention_card, loose_constraints)
