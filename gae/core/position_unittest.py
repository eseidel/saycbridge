#!/usr/bin/python

import unittest2
from position import *


class PositionTest(unittest2.TestCase):
    def test_partner_of(self):
        self.assertEquals(partner_of(NORTH), SOUTH)
        self.assertEquals(partner_of(EAST), WEST)


if __name__ == '__main__':
    unittest2.main()
