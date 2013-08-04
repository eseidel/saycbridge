# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

# FIXME: Hackish enums until we come up with something better.
SUITS = range(4)
CLUBS, DIAMONDS, HEARTS, SPADES = range(4)
NOTRUMP = 4
STRAINS = range(5)

MINORS = (CLUBS, DIAMONDS)
MAJORS = (HEARTS, SPADES)


def suit_name(suit):
    return ("Clubs", "Diamonds", "Hearts", "Spades")[suit]

def suit_color(suit):
    return ("#191970", "#FF4200", "red", "black")[suit]

def suit_entity(suit):
    return ("&clubs;", "&diams;", "&hearts;", "&spades;")[suit]

def suit_char(suit):
    return ("C", "D", "H", "S")[suit]

def suit_from_char(suit_char):
    return {'C': CLUBS, 'D': DIAMONDS, 'H': HEARTS, 'S': SPADES }[suit_char]

def strain_char(char):
    if char == NOTRUMP:
        return 'N'
    return suit_char(char)

def strain_from_char(char):
    return NOTRUMP if char == 'N' else suit_from_char(char)

def other_minor(suit):
    assert suit in MINORS
    return DIAMONDS if suit == CLUBS else CLUBS

def other_major(suit):
    assert suit in MAJORS
    return SPADES if suit == HEARTS else HEARTS
