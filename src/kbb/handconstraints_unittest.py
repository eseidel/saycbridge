# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest2
from kbb.handconstraints import HandConstraints, HonorConstraint
from core.suit import CLUBS, DIAMONDS, HEARTS, SPADES


class HandConstraintsTest(unittest2.TestCase):
    def test_pretty_one_line(self):
        constraints = HandConstraints()
        self.assertEqual(constraints.pretty_one_line(), "?")
        constraints.set_min_hcp(3)
        constraints.set_min_length(CLUBS, 3)
        self.assertEqual(constraints.pretty_one_line(), "3+ hcp, 3+C")

        constraints = HandConstraints()
        constraints.set_min_hcp(3)
        constraints.set_min_length(CLUBS, 3)
        constraints.set_min_length(DIAMONDS, 3)
        self.assertEqual(constraints.pretty_one_line(), "3+ hcp, 3+C 3+D")

    def test_honors_string(self):
        constraints = HandConstraints()
        constraints.set_min_honors(HEARTS, HonorConstraint.FOURTH_ROUND_STOPPER)
        self.assertEqual(constraints.pretty_one_line(), "? hcp, ?H(4rS)")

    def test_is_valid(self):
        constraints = HandConstraints()
        self.assertEqual(constraints.is_valid(), True)

    def test_compute_implied_suit_length_ranges(self):
        constraints = HandConstraints()
        constraints.set_min_length(CLUBS, 3)
        constraints.set_min_length(DIAMONDS, 3)
        constraints.set_min_length(HEARTS, 3)
        self.assertEqual(constraints.max_length(SPADES), 4)

        constraints = HandConstraints()
        constraints.set_max_length(CLUBS, 5)
        constraints.set_longest_suit(CLUBS)
        self.assertEqual(constraints.pretty_one_line(), "? hcp, 4-5C 0-5D 0-5H 0-5S")

        constraints = HandConstraints()
        constraints.set_max_length(CLUBS, 5)
        constraints.set_longest_suit(CLUBS, except_suits=[HEARTS])
        self.assertEqual(constraints.pretty_one_line(), "? hcp, 4-5C 0-5D 0-5S")

        constraints = HandConstraints()
        constraints.set_min_length(DIAMONDS, 3)
        constraints.set_longer_minor(DIAMONDS)
        self.assertEqual(constraints.min_length(DIAMONDS), 3)
        constraints.set_min_length(CLUBS, 4)
        self.assertEqual(constraints.min_length(DIAMONDS), 4)

        constraints = HandConstraints()
        constraints.set_min_length(HEARTS, 3)
        constraints.set_longer_major(HEARTS)
        self.assertEqual(constraints.min_length(HEARTS), 3)
        constraints.set_min_length(SPADES, 4)
        self.assertEqual(constraints.min_length(HEARTS), 4)
