# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import math
import random
import itertools

from suit import *
from card import Card


class Hand(object):
    def __init__(self, cards_by_suit):
        hand_sorter = lambda cards: "".join(sorted(cards, key=Card.index_for_card, reverse=True))
        self.cards_by_suit = map(hand_sorter, map(str.upper, cards_by_suit))
        self._validate()

    def _validate(self):
        assert sum(map(lambda suit: self.length_of_suit(suit), SUITS)) == 13, self.cards_by_suit

    # This is also referred to as "pbn notation": http://www.tistis.nl/pbn/
    # "The cards of each hand are given in the order:  spades, hearts, diamonds, clubs."
    # Gib (and likely other bridge programs) use this notation.
    def shdc_dot_string(self):
        return '.'.join([self.cards_by_suit[suit] for suit in (SPADES, HEARTS, DIAMONDS, CLUBS)])

    # This is the notation we use throughout sayc bridge code.
    def cdhs_dot_string(self):
        return '.'.join([self.cards_by_suit[suit] for suit in (CLUBS, DIAMONDS, HEARTS, SPADES)])

    def play_card(self, suit, card_value):
        assert card_value in self.cards_by_suit[suit]
        self.cards_by_suit[suit] = self.cards_by_suit[suit].replace(card_value, '')

    # FIXME: I'm not sure this belongs here. Eventually users may wish to specify sort.
    def sorted_cards(self):
        sorted_suits = (DIAMONDS, CLUBS, HEARTS, SPADES)
        sorted_cards_by_suit = [sorted(self.cards_by_suit[suit], key=Card.index_for_card) for suit in SUITS]
        return sum([map(lambda value_char: Card(suit, value_char), sorted_cards_by_suit[suit]) for suit in sorted_suits], [])

    @classmethod
    def from_cdhs_string(cls, string):
        return Hand(string.split('.'))

    def high_card_points(self):
        return sum(map(Card.high_card_points, itertools.chain(*self.cards_by_suit)))

    def hcp_in_suit(self, suit):
        return sum(map(Card.high_card_points, self.cards_by_suit[suit]))

    def cards_in_suit(self, suit):
        return self.cards_by_suit[suit]

    def high_card_in_suit(self, suit):
        # FIXME: It's possible we could just return self.cards_in_suit(suit)[0], depending on what cards_in_suit guarantees.
        return sorted(self.cards_in_suit(suit), key=Card.index_for_card)[-1]

    def _count_of_card(self, card):
        return len(filter(lambda cards: card in cards, [self.cards_in_suit(suit) for suit in SUITS]))

    def ace_count(self):
        return self._count_of_card('A')

    def king_count(self):
        return self._count_of_card('K')

    def has_at_least(self, count, cards, suit):
        return len(filter(lambda card: card in cards, self.cards_in_suit(suit))) >= count

    def has_first_round_stopper(self, suit):
        # A singleton is only a stopper if it's an ace.
        return 'A' in self.cards_in_suit(suit)

    def has_second_round_stopper(self, suit):
        # A singly protected king is a 66% chance stopper, so we're not treating it as one.
        # if self.length_of_suit(suit) >= 2:
        #     return self.high_card_in_suit(suit) in "AK"
        cards = self.cards_in_suit(suit)
        if 'K' in cards and 'Q' in cards:  # KQ is a 100% 2nd round stopper.
            return True
        return self.has_first_round_stopper(suit)

    def has_third_round_stopper(self, suit):
        if self.length_of_suit(suit) >= 3:
            # Qxx is a 87.5% stopper (if I did my math correctly).
            return self.high_card_in_suit(suit) in "AKQ"
        return self.has_second_round_stopper(suit)

    def has_fourth_round_stopper(self, suit):
        cards = self.cards_in_suit(suit)
        if len(cards) >= 5:
            # 5 spot cards is almost always a stopper.
            return True
        if len(cards) >= 4:
            # 4 cards in the suit is also almost always a stopper,
            # but for now we're being conservative and requiring an honor.
            return self.high_card_in_suit(suit) in "AKQJT"
        return self.has_third_round_stopper(suit)

    def length_of_suit(self, suit):
        return len(self.cards_by_suit[suit])

    def is_longest_suit(self, suit, except_suits=None):
        except_suits = except_suits or ()
        if suit in except_suits:
            return False
        longest_suit_length = self.length_of_suit(suit)
        for shorter_suit in SUITS:
            if shorter_suit in except_suits:
                continue
            if shorter_suit != suit and self.length_of_suit(shorter_suit) > longest_suit_length:
                return False
        return True

    def suit_lengths(self):
        return map(len, self.cards_by_suit)

    def longest_suits(self):
        longest_suit_length = max(self.suit_lengths())
        return filter(lambda suit: len(self.cards_by_suit[suit]) == longest_suit_length, SUITS)

    def length_points(self):
        # FIXME: Should length_points return high_card_points() - 1 for a flat hand?
        return self.high_card_points() + sum(map(lambda suit: max(self.length_of_suit(suit) - 4, 0), SUITS))

    def _runnability(self, suit):
        fast_winners = 0
        slow_winners = 0
        have_seen_loser = False

        cards_in_hand = self.cards_by_suit[suit]
        for card_index in reversed(range(13)):
            card = Card.card_for_index(card_index)
            if card not in cards_in_hand:
                if have_seen_loser:
                    break
                if card < 1:
                    break
                slow_winners -= 1  # To drive out the adverse holding.
                have_seen_loser = True
            else:
                if have_seen_loser:
                    slow_winners += 1
                else:
                    fast_winners += 1
                    slow_winners += 1
        if slow_winners < fast_winners:
            slow_winners = fast_winners
        return fast_winners, slow_winners

    def tricks(self, partner_min_lengths):
        tricks = 0
        for suit in SUITS:
            length = self.length_of_suit(suit)
            adverse_holding = 13 - length - partner_min_lengths[suit]
            adverse_holding_per_hand = math.ceil(adverse_holding / 2)

            fast_winners, slow_winners = self._runnability(suit)
            if fast_winners >= adverse_holding_per_hand:
                # The suit probably runs.
                tricks += length
            elif slow_winners >= adverse_holding_per_hand:
                tricks += length - 1
            else:
                tricks += slow_winners
        return tricks

    # For this value to be useful, it needs to be compared against the "control-neutral" table
    # http://en.wikipedia.org/wiki/Hand_evaluation#Control_count
    def control_count(self):
        return sum(map(Card.control_count, itertools.chain(*self.cards_by_suit)))

    # FIXME: We shouldn't discount non-working honors for suits that partner has bid (or at least shown stoppers in).
    def _support_point_adjustment_for_non_working_honors(self, trump):
        # We'll overbid if we count holdings like 'K' or 'Qx' for both HCPs and support points.
        point_adjustment = 0
        for suit in SUITS:
            cards = self.cards_by_suit[suit]
            if suit == trump or len(cards) not in (1, 2):
                continue
            if len(cards) == 1:
                if cards[0] != 'A':
                    point_adjustment -= Card.high_card_points(cards[0])
                continue
            if cards[-1] != "K":
                point_adjustment -= Card.high_card_points(cards[-1])
            if cards[0] not in ('A', 'K'):
                point_adjustment -= Card.high_card_points(cards[0])
        return point_adjustment

    def support_points(self, trump):
        assert trump in SUITS, "support_points only makes sense for suited contracts"
        # Support points don't make sense when we don't have a fit, but returning length points
        # here makes some of the logic in responding to a major easier to read.
        if self.length_of_suit(trump) < 3:
            return self.length_points()

        minimum_trump_points = {2: 1, 1: 2, 0: 3}
        four_plus_trump_points = {2: 1, 1: 3, 0: 5}
        short_suit_points = minimum_trump_points if self.length_of_suit(trump) < 4 else four_plus_trump_points
        support_bonus = sum([short_suit_points.get(self.length_of_suit(suit), 0) for suit in SUITS if suit != trump])
        support_bonus += self._support_point_adjustment_for_non_working_honors(trump)
        return support_bonus + self.high_card_points()

    def generic_support_points(self):
        # Support-points are all the same, assuming 3-card trump support.
        return self.support_points(self.longest_suits()[0])

    def is_balanced(self):
        # Balanced hands have no suit longer than 5 and not more than one doubleton.
        # Checking more than one doubleton is sufficient.
        doubletons = 0
        for length in self.suit_lengths():
            if length < 2 or length > 5:
                return False
            if length == 2:
                doubletons += 1
        return doubletons < 2

    def is_flat(self):
        return sorted(self.suit_lengths()) == [3, 3, 3, 4]

    def __repr__(self):
        return "Hand(%s)" % self.cards_by_suit

    def pretty_one_line(self):
        cards_string = ".".join(self.cards_by_suit)
        return "%s (hcp: %s lp: %s sp: %s)" % (cards_string, self.high_card_points(), self.length_points(), self.generic_support_points())
