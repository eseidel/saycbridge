# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from suit import *


class Card(object):
    value_to_index = {}
    for card_value in range(2, 10):
        value_to_index[str(card_value)] = card_value - 2
    value_to_index['T'] = 8
    value_to_index['J'] = 9
    value_to_index['Q'] = 10
    value_to_index['K'] = 11
    value_to_index['A'] = 12

    index_to_value = dict([(index, value) for value, index in value_to_index.items()])

    @classmethod
    def index_for_card(cls, value_char):
        return cls.value_to_index[str(value_char)]

    @classmethod
    def card_for_index(cls, index):
        return cls.index_to_value[index]

    @classmethod
    def identifier_for_card(cls, suit, value):
        return suit * 13 + cls.index_for_card(value)

    @classmethod
    def suit_and_index_from_identifier(cls, identifier):
        suit = identifier / 13
        card_index = identifier - suit * 13
        return (suit, card_index)

    @classmethod
    def suit_and_value_from_identifier(cls, identifier):
        suit, index = cls.suit_and_index_from_identifier(identifier)
        return suit, cls.card_for_index(index)

    @classmethod
    def card_name(cls, suit, value_char):
        return "%s of %s" % (value_char, suit_name(suit))

    @classmethod
    def high_card_points(self, value_char):
        return {'J': 1, 'Q': 2, 'K': 3, 'A': 4}.get(value_char, 0)

    @classmethod
    def control_count(self, value_char):
        return {'K': 1, 'A': 2}.get(value_char, 0)

    def __init__(self, suit, value_char):
        self.suit = suit
        assert suit in SUITS
        self.value_char = value_char
        assert value_char in ('A', 'K', 'Q', 'J', 'T', '9', '8', '7', '6', '5', '4', '3', '2')

    def two_char_name(self):
        return "%s%s" % (self.value_char, suit_char(self.suit))

    @classmethod
    def from_two_char_name(self, name):
        assert len(name) == 2, "%s is not a valid two-char card name" % name
        return Card(suit_from_char(name[1]), name[0])

    def display_value(self):
        if self.value_char == 'T':
            return '10'
        return self.value_char

    def name(self):
        return "%s%s" % (self.display_value(), suit_char(self.suit))

    def index(self):
        return self.index_for_card(self.value_char)

