# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest
from core.position import *


class PositionTest(unittest.TestCase):
    def test_partner(self):
        self.assertEqual(NORTH.partner, SOUTH)
        self.assertEqual(EAST.partner, WEST)

    def test_calls_between(self):
        self.assertEqual(NORTH.calls_between(NORTH), 0)
        self.assertEqual(NORTH.calls_between(EAST), 1)
        self.assertEqual(NORTH.calls_between(SOUTH), 2)
        self.assertEqual(NORTH.calls_between(WEST), 3)


if __name__ == '__main__':
    unittest.main()
