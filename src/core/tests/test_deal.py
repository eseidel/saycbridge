# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest2
from core.deal import Deal


class DealTest(unittest2.TestCase):
    def test_identifier(self):
        deal = Deal.from_string("23456789TJQKA... .23456789TJQKA.. ..23456789TJQKA. ...23456789TJQKA")
        self.assertEquals(deal.identifier, '0000001555555aaaaaabffffff')
        self.assertEquals(deal.pretty_one_line(), Deal.from_identifier(deal.identifier).pretty_one_line())

    def test_random(self):
        # Just make sure the random code path does not assert, and returns something non-None.
        self.assertTrue(bool(Deal.random()))


if __name__ == '__main__':
    unittest2.main()
