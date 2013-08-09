# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.
from collections import defaultdict

class PartialOrdering(object):
    def __init__(self):
        self._values_greater_than = defaultdict(set)

    def make_less_than(self, lesser, greater):
        self._values_greater_than[lesser].add(greater)
        # Need both values to have an entry in the dictionary for the transitive update to not break
        if greater not in self._values_greater_than:
            self._values_greater_than[greater] = set()

    def make_transitive(self):
        has_changed = True
        while has_changed:
            has_changed = False
            for value, greater_values in self._values_greater_than.iteritems():
                new_greater_values = greater_values
                for greater_value in greater_values:
                    new_greater_values = new_greater_values.union(self._values_greater_than[greater_value])
                    if not has_changed and new_greater_values > greater_values:
                        has_changed = True
                self._values_greater_than[value] = new_greater_values

    def less_than(self, left, right):
        # FIXME: enum.py should be asserting when comparing different types
        # but it seems to be silently succeeding in python 2.7.
        if left.enumtype != right.enumtype:
            return right.enumtype in self._values_greater_than.get(left.enumtype, set())
        # Our enums are written highest to lowest, so we use > for less_than. :)
        return left > right
