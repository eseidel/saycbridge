# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest

from z3b import enum
from z3b.rule_compiler import RuleCompiler, _is_not_empty_or_none
from z3b.rules import OneLevelSuitOpening, opening_priorities
from z3b.model import NO_CONSTRAINTS


class EnumTest(unittest.TestCase):
    def test_ordering(self):
        e = enum.Enum('A', 'B')
        self.assertTrue(e.A < e.B)
        self.assertFalse(e.A < e.A)
        self.assertTrue(e.A <= e.A)
        self.assertFalse(e.A > e.A)
        self.assertTrue(e.B > e.A)
        self.assertFalse(e.A < enum.Enum('A', 'B').B)  # values of different enums are unordered


class RuleCompilerTest(unittest.TestCase):
    def test_is_not_empty_or_none(self):
        self.assertFalse(_is_not_empty_or_none(None))
        self.assertFalse(_is_not_empty_or_none([]))
        self.assertFalse(_is_not_empty_or_none({}))
        self.assertTrue(_is_not_empty_or_none([NO_CONSTRAINTS]))
        self.assertTrue(_is_not_empty_or_none(NO_CONSTRAINTS))  # a z3 expression, never compared with ==

    def test_all_priorities_includes_per_call_conditionals(self):
        rule = RuleCompiler.compile(OneLevelSuitOpening)
        self.assertIn(opening_priorities.LongestMinor, rule.all_priorities)
        # Known gap (unchanged): priorities given inside constraints tuples, e.g.
        # '1C': (clubs >= 3, LowerMinor), and rule-level conditional_priorities are not included.
        self.assertNotIn(opening_priorities.LowerMinor, rule.all_priorities)
