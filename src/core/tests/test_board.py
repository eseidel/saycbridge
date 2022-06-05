# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest
from core.board import Board
from core.position import *


class BoardTest(unittest.TestCase):
    @unittest.expectedFailure
    def test_identifier(self):
        board = Board.from_identifier("8-2190948053667986713720276813968-N:NO:")
        # Note how we can handle parsing old-style identfiiers, but we prefer new ones:
        self.assertEqual(board.identifier, "8-0622931ecfe9993de30355dae4")
        # Make sure that parsing new-style identifiers does not raise.
        self.assertTrue(Board.from_identifier("8-0622931ecfe9993de30355dae4"))
        self.assertEqual(board.number, 8)
        self.assertEqual(board.call_history.dealer, NORTH)
        self.assertEqual(board.call_history.vulnerability.name, "None")
        # FIXME: We shouldn't really be using pretty_one_line here since it's likely to change.
        deal_string = "N: AQ8632.6.AKQT4.A (hcp: 19 lp: 22 sp: 25) E: J4.AQ2.73.K86543 (hcp: 10 lp: 12 sp: 11) S: T975.KJT4.92.QT9 (hcp: 6 lp: 6 sp: 7) W: K.98753.J865.J72 (hcp: 5 lp: 6 sp: 5)"
        self.assertEqual(board.deal.pretty_one_line(), deal_string)
