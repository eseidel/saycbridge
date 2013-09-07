# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.call import Pass


class Autobidder(object):
    def __init__(self, bidder):
        self.bidder = bidder

    def _bid_next_hand(self, board):
        position_to_call = board.call_history.position_to_call()
        hand = board.deal.hands[position_to_call]
        selection = self.bidder.call_selection_for(hand, board.call_history)
        call = selection.call if selection else Pass()
        board.call_history.calls.append(call)
        return selection

    def bid_all_hands(self, board, until_position=None):
        call_selections = []
        while not board.call_history.is_complete() and board.call_history.position_to_call() != until_position:
            call_selections.append(self._bid_next_hand(board))
        return call_selections
