# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest

from core.call import Call


class CallTest(unittest.TestCase):
    def test_cmp(self):
        calls = [Call('6N'), Call('2C'), Call('X'), Call('1D'), Call('P'),Call('XX'), Call('7N'), Call('1H'), Call('1N'), Call('1S')]
        expected_sort = [Call('P'), Call('X'), Call('XX'), Call('1D'), Call('1H'), Call('1S'), Call('1N'), Call('2C'), Call('6N'), Call('7N')]
        self.assertEqual(sorted(calls), expected_sort)

    def test_autocase(self):
        self.assertEqual(Call('p'), Call('P'))

    def test_eq(self):
        self.assertEqual(Call('P'), Call('P'))
        test_dict = {}
        test_dict[Call('P')] = 1
        self.assertEqual(test_dict[Call('P')], 1)
        test_dict[Call('1C')] = 2
        self.assertEqual(test_dict[Call('1C')], 2)

    def test_names(self):
        self.assertEqual(list(Call.suited_names_between('1C', '1H')), ['1C', '1D', '1H'])
        self.assertEqual(list(Call.suited_names_between('2D', '4H')), ['2D', '2H', '2S', '3C', '3D', '3H', '3S', '4C', '4D', '4H'])
        self.assertEqual(list(Call.notrump_names_between('1N', '7N')), ['1N', '2N', '3N', '4N', '5N', '6N', '7N'])
        self.assertEqual(list(Call.notrump_names_between('3N', '5N')), ['3N', '4N', '5N'])
