# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.


class PartialOrdering(object):
    def __init__(self):
        self._values_greater_than = {}

    def make_less_than(self, lesser, greater):
        greater_values = self._values_greater_than.get(greater, set()).union(set([greater]))
        self._values_greater_than.setdefault(lesser, set()).update(greater_values)

    def less_than(self, left, right):
        # FIXME: enum.py should be asserting when comparing different types
        # but it seems to be silently succeeding in python 2.7.
        if left.enumtype != right.enumtype:
            return right.enumtype in self._values_greater_than.get(left.enumtype, set())
        # Our enums are written highest to lowest, so we use > for less_than. :)
        return left > right
