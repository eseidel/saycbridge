# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest2
from core.call import Call
from core.callhistory import CallHistory, Vulnerability
from core.position import *
from core.suit import *


class VulnerabilityTest(unittest2.TestCase):
    def test_vunerability_from_board_number(self):
        expectations = {
            1: 'None',
            2: 'N-S',
            3: 'E-W',
            4: 'Both',
            5: 'N-S',
            6: 'E-W',
            7: 'Both',
            8: 'None',
            9: 'E-W',
            10: 'Both',
            11: 'None',
            12: 'N-S',
            13: 'Both',
            14: 'None',
            15: 'N-S',
            16: 'E-W',
            17: 'None',
            31: 'N-S',
            33: 'None',
        }
        for number, expected_vulnerability in list(expectations.items()):
            self.assertEquals(Vulnerability.from_board_number(number).name, expected_vulnerability)


class CallHistoryTest(unittest2.TestCase):

    def _assert_declarer(self, history_string, dealer, declarer):
        self.assertEquals(CallHistory.from_string(history_string, dealer.char).declarer(), declarer)

    def test_declarer(self):
        self._assert_declarer("", NORTH, None)
        self._assert_declarer("P P P P", NORTH, None)
        self._assert_declarer("1C", NORTH, NORTH)
        self._assert_declarer("1C P P P", NORTH, NORTH)
        self._assert_declarer("1C P 2C", NORTH, NORTH)
        self._assert_declarer("1C P 1S", NORTH, SOUTH)
        self._assert_declarer("P 1C P 1D P", NORTH, WEST)
        self._assert_declarer("P 1C P 1D P", EAST, NORTH)
        self._assert_declarer("P 1C P 1D P", WEST, SOUTH)

    def test_position_to_call(self):
        self.assertEquals(CallHistory.from_string("").position_to_call(), NORTH)
        self.assertEquals(CallHistory.from_string("P").position_to_call(), EAST)
        self.assertEquals(CallHistory.from_string("1N P").position_to_call(), SOUTH)
        self.assertEquals(CallHistory.from_string("1N P 2C").position_to_call(), WEST)
        self.assertEquals(CallHistory.from_string("1N P 2C P").position_to_call(), NORTH)
        self.assertEquals(CallHistory.from_string("1N P 2C P 2D").position_to_call(), EAST)

    def test_last_to_call(self):
        self.assertEquals(CallHistory.from_string("").last_to_call, None)
        self.assertEquals(CallHistory.from_string("P").last_to_call, NORTH)
        self.assertEquals(CallHistory.from_string("1N P").last_to_call, EAST)
        self.assertEquals(CallHistory.from_string("1N P 2C").last_to_call, SOUTH)
        self.assertEquals(CallHistory.from_string("1N P 2C P").last_to_call, WEST)
        self.assertEquals(CallHistory.from_string("1N P 2C P 2D").last_to_call, NORTH)

    def test_is_passout(self):
        self.assertEquals(CallHistory.from_string("").is_passout(), False)
        self.assertEquals(CallHistory.from_string("P").is_passout(), False)
        self.assertEquals(CallHistory.from_string("P P").is_passout(), False)
        self.assertEquals(CallHistory.from_string("P P P").is_passout(), False)
        self.assertEquals(CallHistory.from_string("P P P P").is_passout(), True)
        self.assertEquals(CallHistory.from_string("P 1N P P P").is_passout(), False)

    def test_copy_with_partial_history(self):
        history = CallHistory.from_string("P P 1N P P P")
        self.assertEquals(len(history.calls), 6)
        self.assertEquals(len(history.copy_with_partial_history(0).calls), 0)
        self.assertEquals(len(history.copy_with_partial_history(2).calls), 2)
        self.assertEquals(len(history.copy_with_partial_history(-2).calls), 4)
        partial_history = history.copy_with_partial_history(3)
        self.assertEquals(len(history.calls), 6)
        self.assertEquals(len(partial_history.calls), 3)
        partial_history.calls.append(None)  # Invalid, but fine for testing.
        self.assertEquals(len(history.calls), 6)
        self.assertEquals(len(partial_history.calls), 4)

    def _assert_competative_auction(self, history_string, is_competative):
        self.assertEquals(CallHistory.from_string(history_string).competative_auction(), is_competative)

    def test_competative_auction(self):
        self._assert_competative_auction("1D P 1H P", False)

    def _assert_opener(self, history_string, dealer, opener):
        self.assertEquals(CallHistory.from_string(history_string, dealer.char).opener(), opener)

    def test_opener(self):
        self._assert_opener("P 1C P 1D P", NORTH, EAST)
        self._assert_opener("P 1C P 1D P", EAST, SOUTH)
        self._assert_opener("P 1C P 1D P", WEST, NORTH)

    def test_from_identifier(self):
        self.assertEqual(CallHistory.from_identifier('E:EW:P').identifier, CallHistory.from_string('P', 'E', 'E-W').identifier)
        # Test that from_identifier is forgiving of a missing trailing colon
        self.assertEqual(CallHistory.from_identifier('E:EW:').identifier, CallHistory.from_string('', 'E', 'E-W').identifier)
        self.assertEqual(CallHistory.from_identifier('E:EW').identifier, CallHistory.from_string('', 'E', 'E-W').identifier)
        # Test that from_identifier is forgiving of a trailing comma.
        self.assertEqual(CallHistory.from_identifier('N:NO:P,').calls_string(), "P")

    def test_can_double(self):
        self.assertTrue(CallHistory.from_string("1S 2H 2S").can_double())

    def _assert_is_legal_call(self, history_string, call_name, is_legal=True):
        call_history = CallHistory.from_string(history_string)
        call = Call.from_string(call_name)
        self.assertEquals(call_history.is_legal_call(call), is_legal)

    def test_is_legal_call(self):
        self._assert_is_legal_call("", "P", True)
        self._assert_is_legal_call("", "X", False)
        self._assert_is_legal_call("", "XX", False)
        self._assert_is_legal_call("P", "X", False)
        self._assert_is_legal_call("P", "X", False)
        self._assert_is_legal_call("1N", "1C", False)
        self._assert_is_legal_call("1N", "XX", False)
        self._assert_is_legal_call("1N X", "X", False)
        self._assert_is_legal_call("1N X", "XX", True)
        self._assert_is_legal_call("P 1D 2S P", "X", False)

    def test_empty_for_board_number(self):
        self.assertEquals(CallHistory.empty_for_board_number(1).dealer, NORTH)
        self.assertEquals(CallHistory.empty_for_board_number(6).dealer, EAST)
        self.assertEquals(CallHistory.empty_for_board_number(16).dealer, WEST)


if __name__ == '__main__':
    unittest2.main()
