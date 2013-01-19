#!/usr/bin/python

import unittest
from core.hand import Hand
from core.suit import *


class HandTest(unittest.TestCase):
    def _assert_balanced(self, hand_string, balanced):
        self.assertEquals(Hand.from_cdhs_string(hand_string).is_balanced(), balanced)

    def test_is_balanced(self):
        self._assert_balanced("732.Q.AJ.AKJ9843", False)
        self._assert_balanced("73.Q2.AJ.AKJ9843", False)
        self._assert_balanced("732.Q32.AJ.AKJ98", True)

    def _assert_flat(self, hand_string, flat):
        self.assertEquals(Hand.from_cdhs_string(hand_string).is_flat(), flat)

    def test_is_flat(self):
        self._assert_flat("732.Q.AJ.AKJ9843", False)
        self._assert_flat("732.Q32.AJ.AKJ98", False)
        self._assert_flat("732.Q32.AJ8.AKJ9", True)
        self._assert_flat("A732.Q32.AJ8.AKJ", True)
        self._assert_flat("A73.AQ32.AJ8.AKJ", True)
        self._assert_flat("952.QT87.A86.Q52", True)

    def _assert_non_working_honor_adjustment(self, hand_string, trump, expected_adjustment):
        hand = Hand.from_cdhs_string(hand_string)
        self.assertEquals(hand._support_point_adjustment_for_non_working_honors(trump), expected_adjustment)

    def test_support_point_adjustment_for_non_working_honors(self):
        self._assert_non_working_honor_adjustment("AKJ52.J.J9743.54", HEARTS, -1)
        self._assert_non_working_honor_adjustment("AKJ52.Q.J9743.54", HEARTS, -2)
        self._assert_non_working_honor_adjustment("AKJ52.K.J9743.54", HEARTS, -3)
        self._assert_non_working_honor_adjustment("AKJ52.A.J9743.54", HEARTS, 0)
        self._assert_non_working_honor_adjustment("AKJ52.KQ.J974.54", HEARTS, -2)
        self._assert_non_working_honor_adjustment("AKJ52.KJ.J974.54", HEARTS, -1)
        self._assert_non_working_honor_adjustment("AKJ52.K9.J974.54", HEARTS, 0)
        self._assert_non_working_honor_adjustment("AKJ52.QJ.J974.54", HEARTS, -3)
        self._assert_non_working_honor_adjustment("AKJ52.Q9.J974.54", HEARTS, -2)

    def test_support_points(self):
        self.assertEquals(Hand.from_cdhs_string("AKJ52.J.J9743.54").support_points(HEARTS), 13)
        self.assertEquals(Hand.from_cdhs_string("AKJ52.J.J9743.54").generic_support_points(), 13)
        self.assertEquals(Hand.from_cdhs_string("AKJ52..J9743.J54").generic_support_points(), 15)

    def _hand_with_clubs(self, clubs_string):
        spade_filler_string = 'AKQJT98765432'
        hand_string = clubs_string + '...' + spade_filler_string[:-len(clubs_string)]
        return Hand.from_cdhs_string(hand_string)

    def _assert_stopper(self, cards_string, expected_round):
        hand = self._hand_with_clubs(cards_string)
        self.assertEquals(hand.has_fourth_round_stopper(CLUBS), bool(expected_round) and expected_round <= 4)
        self.assertEquals(hand.has_third_round_stopper(CLUBS), bool(expected_round) and expected_round <= 3)
        self.assertEquals(hand.has_second_round_stopper(CLUBS), bool(expected_round) and expected_round <= 2)
        self.assertEquals(hand.has_first_round_stopper(CLUBS), bool(expected_round) and expected_round <= 1)

    def test_stoppers(self):
        self._assert_stopper("2", None)
        self._assert_stopper("85", None)
        self._assert_stopper("A", 1)
        self._assert_stopper("K", None)
        self._assert_stopper("K2", None)  # Kx is only a 66% chance stopper.
        self._assert_stopper("KQ", 2)
        self._assert_stopper("QJ", None)
        self._assert_stopper("QJ2", 3)
        self._assert_stopper("T765", 4)  # Currently we count Txxx as a stopper, but not 9xxx.
        self._assert_stopper("9765", None)
        self._assert_stopper("J765", 4)
        self._assert_stopper("87654", 4)

    def test_pbn_string(self):
        reverse_pbn = "AKJ52.J.J9743.54"
        hand = Hand.from_cdhs_string(reverse_pbn)
        self.assertEquals(hand.reverse_pbn_string(), reverse_pbn)
        self.assertEquals(hand.pbn_string(), "54.J9743.J.AKJ52")


if __name__ == '__main__':
    unittest.main()
