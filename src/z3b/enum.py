# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import functools

class Enum(object):
    @functools.total_ordering
    class EnumValue(object):
        def __init__(self, enum, index, key):
            self.enum = enum
            self.index = index
            self.key = key

        def __repr__(self):
            return self.key

        def __le__(self, other):
            return self.enum == other.enum and self.index < other.index

    def __init__(self, *args):
        self._count = 0
        self._values = [None] * len(args)
        for arg in args:
            value = Enum.EnumValue(self, self._count, arg)

            self._values[self._count] = value
            setattr(self, arg, value)

            self._count += 1

    def get(self, arg):
        return getattr(self, arg)

    def __len__(self):
        return self._count

    def __getitem__(self, index):
        return self._values[index]

    def __iter__(self):
        return iter(self._values)
