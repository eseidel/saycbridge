#!/usr/bin/python

import unittest
from position import *


class PositionTest(unittest.TestCase):
    def test_partner_of(self):
        self.assertEquals(partner_of(NORTH), SOUTH)
        self.assertEquals(partner_of(EAST), WEST)


if __name__ == '__main__':
    unittest.main()
