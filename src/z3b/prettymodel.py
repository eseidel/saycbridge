# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b.model import _honor_vars
from core.hand import Hand
from core.suit import SUITS
import z3

def _suit_index(name):
    suits = ('clubs', 'diamonds', 'hearts', 'spades')
    if name not in suits:
        return len(suits) + 1 # Sort last
    return suits.index(name)


def _decl_cmp(*args):
    names = map(lambda key: key.name(), args)
    # Sort suit names first:
    suit_cmp_result = cmp(*map(_suit_index, names))
    if suit_cmp_result:
        return suit_cmp_result
    # Sort names without _ in them to the top.
    are_primary = map(lambda name: name.find("_") != -1, names)
    cmp_result = cmp(*are_primary)
    if cmp_result:
        return cmp_result
    return cmp(*names)


def pretty_print_model(model):
    for decl in sorted(model.decls(), cmp=_decl_cmp):
        if model[decl].as_long() != 0:
            print "%s: %s" % (decl, model[decl])


def _cards_from_model(suit, model):
    honor_cards = ""
    for honor_var, card_name in zip(_honor_vars(suit), ('A', 'K', 'Q', 'J', 'T')):
        if model.eval(honor_var).as_long():
            honor_cards += card_name

    suit_var = z3.Int(suit.name.lower())
    suit_count = model.eval(suit_var).as_long()
    assert len(honor_cards) <= suit_count
    # We could use x's, except Hand() would barf trying to parse those.
    return honor_cards + "".join([str(spot_card) for spot_card in range(2, 2 + suit_count - len(honor_cards))])


# model is the result of solver.model()
def hand_from_model(model):
    return Hand(map(lambda suit: _cards_from_model(suit, model), SUITS))
