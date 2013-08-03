# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import random
from deal import Deal
from core.callhistory import CallHistory


class Board(object):
    def __init__(self, number=None, deal=None, call_history=None):
        self.number = number or 1
        self.deal = deal or Deal.random()
        self.call_history = call_history or CallHistory.empty_for_board_number(number)

    def identifier(self):
        identifier = "%s-%s" % (self.number, self.deal.identifier())
        if self.call_history.calls:
            identifier += ":%s" % (self.call_history.comma_separated_calls())
        return identifier

    @classmethod
    def from_identifier(self, identifier):
        components = identifier.split("-")
        if len(components) == 2:
            (board_number_string, deal_and_history_identifier) = components
            if ':' in deal_and_history_identifier:
                deal_identifier, call_history_identifier = deal_and_history_identifier.split(':')
                # We have to do a bit of a dance to convert from the board url system that
                # the JS code uses to the one the python uses.
                call_history = CallHistory.from_board_number_and_calls_string(int(board_number_string), call_history_identifier)
            else:
                deal_identifier = deal_and_history_identifier
                call_history = CallHistory.empty_for_board_number(int(board_number_string))
        else:
            (board_number_string, deal_identifier, call_history_identifier) = components
            call_history = CallHistory.from_identifier(call_history_identifier)

        board_number = int(board_number_string)
        deal = Deal.from_identifier(deal_identifier)
        return Board(number=board_number, deal=deal, call_history=call_history)

    @classmethod
    def random(cls):
        board_number = random.randint(1, 16)
        # Will automatically deal random if not passed a Deal.
        return Board(board_number)
