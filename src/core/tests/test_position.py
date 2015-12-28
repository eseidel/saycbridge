# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest2
from core.position import *


class PositionTest(unittest2.TestCase):
    def test_partner(self):
        self.assertEquals(NORTH.partner, SOUTH)
        self.assertEquals(EAST.partner, WEST)

    def test_calls_between(self):
        self.assertEquals(NORTH.calls_between(NORTH), 0)
        self.assertEquals(NORTH.calls_between(EAST), 1)
        self.assertEquals(NORTH.calls_between(SOUTH), 2)
        self.assertEquals(NORTH.calls_between(WEST), 3)


if __name__ == '__main__':
    unittest2.main()
