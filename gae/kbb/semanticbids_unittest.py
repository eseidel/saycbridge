#!/usr/bin/python

import unittest
from kbb.semanticbids import SemanticBid


class SemanticBidTest(unittest.TestCase):
    def test_pretty_one_line(self):
        bid = SemanticBid("1C", opening=True)
        self.assertEqual(bid.pretty_one_line(), "1C opening")
        self.assertEqual(bid.pretty_one_line(include_bid_name=False), "opening")
