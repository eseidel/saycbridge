from __future__ import division
from __future__ import absolute_import
# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from builtins import str
from builtins import map
from builtins import range
from builtins import object
from past.utils import old_div
from .position import *
from .suit import Suit, SUITS
from .card import Card
from .hand import Hand
from core.callhistory import CallHistory

import random

import json


class Deal(object):
    def __init__(self, hands):
        self.hands = hands
        self._validate()

    @classmethod
    def _empty_hands(self):
        hands = []
        for position in POSITIONS:
            hands.append(["" for suit in SUITS])
        return hands

    @classmethod
    def random(cls):
        # FIXME: A better random would generate a random identifier
        # and use from_identifier.  Howver our current identifier
        # space is not compact.  We can generate identifiers
        # which are not valid deals.
        hands = cls._empty_hands()
        shuffled_cards = list(range(52))
        random.shuffle(shuffled_cards)
        for index_in_deck, card_identifier in enumerate(shuffled_cards):
            position = index_in_deck % len(POSITIONS)
            suit, card = Card.suit_and_value_from_identifier(card_identifier)
            hands[position][suit.index] += card
        return Deal(list(map(Hand, hands)))

    @classmethod
    def from_string(cls, string):
        hand_strings = string.split(' ')
        # Deal takes strings, not hand objects, currently.
        return Deal(list(map(Hand.from_cdhs_string, hand_strings)))

    @classmethod
    def from_hex_identifier(cls, identifier):
        hands = cls._empty_hands()
        hexChars = '0123456789abcdef'
        for charIndex, hexChar in enumerate(identifier):
            hexIndex = hexChars.index(hexChar)
            highHandIndex = old_div(hexIndex, 4)
            lowHandIndex = hexIndex - highHandIndex * 4
            highSuit, highCard = Card.suit_and_value_from_identifier(charIndex * 2 + 0)
            lowSuit, lowCard = Card.suit_and_value_from_identifier(charIndex * 2 + 1)
            hands[highHandIndex][highSuit.index] += highCard
            hands[lowHandIndex][lowSuit.index] += lowCard
        return Deal(list(map(Hand, hands)))

    @classmethod
    def from_old_identifier(cls, identifier):
        identifier = int(identifier)
        hands = cls._empty_hands()
        for card_identifier in reversed(list(range(52))):
            power_of_four = pow(4, card_identifier)
            position = old_div(identifier, power_of_four)
            identifier -= power_of_four * position
            suit, card = Card.suit_and_value_from_identifier(card_identifier)
            hands[position][suit.index] += card
        return Deal(list(map(Hand, hands)))

    @classmethod
    def from_identifier(cls, identifier):
        if len(identifier) > 29:
            return cls.from_old_identifier(identifier)
        return cls.from_hex_identifier(identifier)

    @property
    def identifier(self):
        position_for_card = [None for _ in range(52)]
        for position_index, hand in enumerate(self.hands):
            for suit_index, cards in enumerate(hand.cards_by_suit_index):
                for card in cards:
                    suit = Suit.from_index(suit_index)
                    card_identifier = Card.identifier_for_card(suit, card)
                    position_for_card[card_identifier] = position_index

        # position_for_card represents a 52-digit number in base 4
        # We're going to split it into 4-digit hunks and convert to base 16.
        identifier = ""
        hex_chars = '0123456789abcdef'
        for offset in range(26):
            # A single hex digit encodes 4 bits where as our previous encoding was 2.
            hex_index = position_for_card[offset * 2 + 0] * 4 + position_for_card[offset * 2 + 1]
            identifier += hex_chars[hex_index]
        return identifier

    # This is not maximally efficient, we could use
    # combinadics to use 96bits instead of 104.
    @property
    def old_identifier(self):
        # We're constructing a 52 digit number in base 4,
        # converted to base-10, its our identifier.
        identifier = 0
        for position, hand in enumerate(self.hands):
            for suit_index, cards in enumerate(hand.cards_by_suit_index):
                for card in cards:
                    suit = Suit.from_index(suit_index)
                    card_identifier = Card.identifier_for_card(suit, card)
                    identifier += position * pow(4, card_identifier)
        return str(identifier)

    def to_json(self, **kwargs):
        deal_dict = dict([(position.name.lower(), hand.cdhs_dot_string()) for position, hand in enumerate(self.hands)])
        return json.dumps(deal_dict, **kwargs)

    def pretty_one_line(self):
        pretty_position = lambda position: "%s: %s" % (position.char, self.hand_for(position).pretty_one_line())
        return " ".join(map(pretty_position, POSITIONS))

    def hand_for(self, position):
        return self.hands[position.index]

    def _validate(self):
        all_cards = set()
        for hand in self.hands:
            for suit in SUITS:
                for card in hand.cards_in_suit(suit):
                    card_identifier = Card.identifier_for_card(suit, card)
                    assert card_identifier not in all_cards, ("Already seen %s" % Card.card_name(suit, card))
                    all_cards.add(card_identifier)
        assert len(all_cards) == 52
