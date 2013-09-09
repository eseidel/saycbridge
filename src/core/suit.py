# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from third_party.memoized import memoized


class Strain(object):
    def __init__(self, index, this_should_not_be_called_directly=False):
        assert(this_should_not_be_called_directly)
        # Python's built-in __lt__ happens to work since all we do is store an index.
        self.index = index

    ALL_NAMES = ('Clubs', 'Diamonds', 'Hearts', 'Spades', 'Notrump')
    All_CHARS = ('C', 'D', 'H', 'S', 'N')

    def is_suit(self):
        return self in SUITS

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Strain(%s)" % self.name

    def __eq__(self, other):
        return other and self.index == other.index

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.index)

    def __cmp__(self, other):
        return cmp(self.index, other.index)

    @staticmethod
    @memoized
    def from_index(index):
        assert index in range(5)
        return Strain(index, this_should_not_be_called_directly=True)

    @classmethod
    def from_name(cls, name):
        return cls.from_index(cls.ALL_NAMES.index(name))

    @classmethod
    def from_char(cls, char):
        return cls.from_index(cls.All_CHARS.index(char))

    @property
    def name(self):
        return self.ALL_NAMES[self.index]

    @property
    def char(self):
        return self.name[0]

    def other_minor(self):
        assert suit in MINORS
        return DIAMONDS if self == CLUBS else CLUBS

    def other_major(self):
        assert self in MAJORS
        return SPADES if self == HEARTS else HEARTS


# These are never instantiated, but rather just used to add asserts
# Cards use Suits, but Calls use Strains.  They both end up using
# Strain objects, but Card-related calls use Suit.from_* to catch typos.
class Suit(Strain):
    SUIT_NAMES = ('Clubs', 'Diamonds', 'Hearts', 'Spades')
    SUIT_CHARS = ('C', 'D', 'H', 'S')

    @classmethod
    def from_index(cls, index):
        assert index in range(4)
        return Strain.from_index(index)

    @classmethod
    def from_char(cls, char):
        assert char in cls.SUIT_CHARS
        return Strain.from_char(char)


# FIXME: These should eventually all move onto Strain e.g. Strain.SUITS, Strain.MINORS, etc.
SUITS = map(Strain.from_index, range(4))
CLUBS, DIAMONDS, HEARTS, SPADES = map(Strain.from_index, range(4))
NOTRUMP = Strain.from_index(4)
STRAINS = map(Strain.from_index, range(5))

MINORS = (CLUBS, DIAMONDS)
MAJORS = (HEARTS, SPADES)
