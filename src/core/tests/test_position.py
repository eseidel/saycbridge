# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest2
from core.position import *


class PositionTest(unittest2.TestCase):
    def test_partner_of(self):
        self.assertEquals(partner_of(NORTH), SOUTH)
        self.assertEquals(partner_of(EAST), WEST)


if __name__ == '__main__':
    unittest2.main()
