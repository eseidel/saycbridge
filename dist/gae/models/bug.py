# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from google.appengine.ext import db

from core.board import Board
from third_party.memoized import memoized
from core.autobidder import Autobidder


class Bug(db.Model):
    created = db.DateTimeProperty(auto_now_add=True)
    url = db.StringProperty()
    description = db.StringProperty()
    status = db.StringProperty()
    board_identifier = db.StringProperty()
    calls_string = db.StringProperty()  # Bid History at time of filing.
    autobid_string = db.StringProperty()  # Autobid History at time of filing.

    def board(self):
        if not self.board_identifier:
            return None
        try:
            return Board.from_identifier(self.board_identifier)
        except ValueError, e:
            pass
        return None

    # FIXME: I suspect this is a layering violation.
    @memoized
    def current_autobid(self):
        board = self.board()
        if not board:
            return None
        # Empty the bid history of all bids
        board.call_history = board.call_history.copy_with_partial_history(0)
        Autobidder().bid_all_hands(board)
        return board.call_history.calls_string()
