# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest

from core.callhistory import CallHistory
from core.position import NORTH, EAST
from z3b.bidder import History, HistoryCache, Interpreter


class HistoryCacheTest(unittest.TestCase):
    def test_root_history_keeps_dealer_and_vulnerability(self):
        cache = HistoryCache()
        call_history = CallHistory.from_string("1N P", dealer_char='E', vulnerability_string='N-S')
        history, remaining = cache.lookup(call_history)
        self.assertEqual(remaining, call_history.calls)
        self.assertEqual(history.call_history.calls, [])
        self.assertEqual(history.call_history.dealer, EAST)
        self.assertEqual(history.call_history.vulnerability.name, 'N-S')

    def test_same_calls_different_dealer_are_different_entries(self):
        cache = HistoryCache()
        interpreter = Interpreter()
        north = CallHistory.from_string("1N P", dealer_char='N')
        east = CallHistory.from_string("1N P", dealer_char='E')
        for call_history in (north, east):
            with interpreter.create_history(call_history) as history:
                cache.add(history)
        cached_north, remaining_north = cache.lookup(north)
        cached_east, remaining_east = cache.lookup(east)
        self.assertEqual(remaining_north, [])
        self.assertEqual(remaining_east, [])
        self.assertIsNot(cached_north, cached_east)
        self.assertEqual(cached_north.call_history.dealer, NORTH)
        self.assertEqual(cached_east.call_history.dealer, EAST)

    def test_cached_root_is_not_a_match(self):
        cache = HistoryCache()
        call_history = CallHistory.from_string("1N P")
        cache.add(History(call_history=call_history.copy_with_partial_history(0)))
        history, remaining = cache.lookup(call_history)
        self.assertEqual(remaining, call_history.calls)
        self.assertEqual(history.call_history.calls, [])

    def test_longest_prefix_wins(self):
        cache = HistoryCache()
        interpreter = Interpreter()
        with interpreter.create_history(CallHistory.from_string("1N P 2C P")) as history:
            cache.add(history)
        history, remaining = cache.lookup(CallHistory.from_string("1N P 2C P 2H P"))
        self.assertEqual([call.name for call in remaining], ['2H', 'P'])
        self.assertEqual(history.call_history.calls_string(), "1N P 2C P")
