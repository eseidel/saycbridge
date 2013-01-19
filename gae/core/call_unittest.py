#!/usr/bin/python

import unittest

from core.call import Call


class CallTest(unittest.TestCase):
    def test_cmp(self):
        calls = [Call('6N'), Call('2C'), Call('X'), Call('1D'), Call('P'),Call('XX'), Call('7N'), Call('1H'), Call('1N'), Call('1S')]
        expected_sort = [Call('P'), Call('X'), Call('XX'), Call('1D'), Call('1H'), Call('1S'), Call('1N'), Call('2C'), Call('6N'), Call('7N')]
        self.assertEqual(sorted(calls), expected_sort)
