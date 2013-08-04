# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest2
from kbb.semanticbids import SemanticBid


class SemanticBidTest(unittest2.TestCase):
    def test_pretty_one_line(self):
        bid = SemanticBid("1C", opening=True)
        self.assertEqual(bid.pretty_one_line(), "1C opening")
        self.assertEqual(bid.pretty_one_line(include_bid_name=False), "opening")
