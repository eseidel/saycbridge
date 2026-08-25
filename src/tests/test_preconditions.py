# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest

from core.call import Call
from core.callhistory import CallHistory
from z3b.bidder import Interpreter
from z3b.preconditions import IsGame, LastBidWasBelowGame, LastBidWasGameOrAbove


class PreconditionsTest(unittest.TestCase):
    def _history(self, calls):
        return Interpreter().create_history(CallHistory.from_string(calls))

    def test_is_game(self):
        with self._history("1H P") as history:
            self.assertTrue(IsGame().fits(history, Call('4H')))
            self.assertTrue(IsGame().fits(history, Call('3N')))
            self.assertTrue(IsGame().fits(history, Call('5C')))
            self.assertFalse(IsGame().fits(history, Call('3H')))
            self.assertFalse(IsGame().fits(history, Call('4C')))
            self.assertFalse(IsGame().fits(history, Call('P')))
            self.assertTrue(LastBidWasBelowGame().fits(history, Call('2H')))
        with self._history("1H P 4H P") as history:
            self.assertTrue(LastBidWasGameOrAbove().fits(history, Call('P')))
