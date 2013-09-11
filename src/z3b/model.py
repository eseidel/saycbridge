# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b import enum
import core.suit as suit
import z3

spades, hearts, diamonds, clubs = z3.Ints('spades hearts diamonds clubs')

ace_of_spades, king_of_spades, queen_of_spades, jack_of_spades, ten_of_spades = z3.Ints(
    'ace_of_spades king_of_spades queen_of_spades jack_of_spades ten_of_spades')
ace_of_hearts, king_of_hearts, queen_of_hearts, jack_of_hearts, ten_of_hearts = z3.Ints(
    'ace_of_hearts king_of_hearts queen_of_hearts jack_of_hearts ten_of_hearts')
ace_of_diamonds, king_of_diamonds, queen_of_diamonds, jack_of_diamonds, ten_of_diamonds = z3.Ints(
    'ace_of_diamonds king_of_diamonds queen_of_diamonds jack_of_diamonds ten_of_diamonds')
ace_of_clubs, king_of_clubs, queen_of_clubs, jack_of_clubs, ten_of_clubs = z3.Ints(
    'ace_of_clubs king_of_clubs queen_of_clubs jack_of_clubs ten_of_clubs')

high_card_points, points, playing_points = z3.Ints('high_card_points points playing_points')

points_supporting_spades, points_supporting_hearts, points_supporting_diamonds, points_supporting_clubs = z3.Ints(
    'points_supporting_spades points_supporting_hearts points_supporting_diamonds points_supporting_clubs')

void_in_spades, void_in_hearts, void_in_diamonds, void_in_clubs = z3.Ints(
    'void_in_spades void_in_hearts void_in_diamonds void_in_clubs')
singleton_in_spades, singleton_in_hearts, singleton_in_diamonds, singleton_in_clubs = z3.Ints(
    'singleton_in_spades singleton_in_hearts singleton_in_diamonds singleton_in_clubs')
doubleton_in_spades, doubleton_in_hearts, doubleton_in_diamonds, doubleton_in_clubs = z3.Ints(
    'doubleton_in_spades doubleton_in_hearts doubleton_in_diamonds doubleton_in_clubs')

voids, singletons, doubletons = z3.Ints('voids singletons doubletons')


def named_count_expr(count_name, count):
    exprs = []
    suit_names = [s.name.lower() for s in suit.SUITS]
    suit_count_vars = map(z3.Int, suit_names) # spades, etc.
    suit_matches_count_vars = map(z3.Int, map((count_name + "_in_{}").format, suit_names)) # void_in_spades, etc.
    exprs = [
        # FIXME: Can z3 support writing this as "void_in_spades == (spades == 0)"?
        z3.Or(z3.And(suit_count == count, suit_matches_count == 1), z3.And(suit_count != count, suit_matches_count == 0))
            for suit_count, suit_matches_count in zip(suit_count_vars, suit_matches_count_vars)
    ]
    exprs.append(z3.Int(count_name + "s") == sum(suit_matches_count_vars))
    return z3.And(*exprs)


def constrain_honors_expr():
    exprs = []
    for suit_name in [s.name.lower() for s in suit.SUITS]:
        suit_var = z3.Int(suit_name)
        honor_names = ('ace', 'king', 'queen', 'jack', 'ten')
        honor_name_vars = map(z3.Int, map(("{}_of_" + suit_name).format, honor_names))
        # The easiest way to have an Int var and constrain it to bool values is to just:
        # z3.And(0 <= ace_of_spades, ace_of_spades <= 1)
        exprs.extend([z3.And(0 <= honor_name_var, honor_name_var <= 1) for honor_name_var in honor_name_vars])
        # Also make sure that total number of honors is <= total number of cards
        exprs.append(sum(honor_name_vars) <= suit_var)
    return z3.And(*exprs)


axioms = [
    spades + hearts + diamonds + clubs == 13,
    spades >= 0,
    hearts >= 0,
    diamonds >= 0,
    clubs >= 0,
    0 <= high_card_points, high_card_points <= 37,
    points == high_card_points,
    high_card_points <= playing_points,
    playing_points <= 55, # Just to make the model finite.

    named_count_expr('void', 0),
    named_count_expr('singleton', 1),
    named_count_expr('doubleton', 2),
    constrain_honors_expr(),

    z3.Or(
        z3.And(spades <= 2, points_supporting_spades == high_card_points),
        z3.And(spades == 3, points_supporting_spades == high_card_points + doubletons + 2 * singletons + 3 * voids),
        z3.And(spades >= 4, points_supporting_spades == high_card_points + doubletons + 3 * singletons + 5 * voids),
    ),

    z3.Or(
        z3.And(hearts <= 2, points_supporting_hearts == high_card_points),
        z3.And(hearts == 3, points_supporting_hearts == high_card_points + doubletons + 2 * singletons + 3 * voids),
        z3.And(hearts >= 4, points_supporting_hearts == high_card_points + doubletons + 3 * singletons + 5 * voids),
    ),

    z3.Or(
        z3.And(diamonds <= 2, points_supporting_diamonds == high_card_points),
        z3.And(diamonds == 3, points_supporting_diamonds == high_card_points + doubletons + 2 * singletons + 3 * voids),
        z3.And(diamonds >= 4, points_supporting_diamonds == high_card_points + doubletons + 3 * singletons + 5 * voids),
    ),

    z3.Or(
        z3.And(clubs <= 2, points_supporting_clubs == high_card_points),
        z3.And(clubs == 3, points_supporting_clubs == high_card_points + doubletons + 2 * singletons + 3 * voids),
        z3.And(clubs >= 4, points_supporting_clubs == high_card_points + doubletons + 3 * singletons + 5 * voids),
    ),

    4 * ace_of_spades   + 3 * king_of_spades   + 2 * queen_of_spades   + 1 * jack_of_spades   +
    4 * ace_of_hearts   + 3 * king_of_hearts   + 2 * queen_of_hearts   + 1 * jack_of_hearts   +
    4 * ace_of_diamonds + 3 * king_of_diamonds + 2 * queen_of_diamonds + 1 * jack_of_diamonds +
    4 * ace_of_clubs    + 3 * king_of_clubs    + 2 * queen_of_clubs    + 1 * jack_of_clubs    == high_card_points
]

min_hcp_for_open = 8

def _expr_for_point_rule(count):
    return z3.And(
        high_card_points >= min_hcp_for_open,
        playing_points >= 12,
        z3.Or(
            spades + hearts + high_card_points >= count,
            spades + diamonds + high_card_points >= count,
            spades + clubs + high_card_points >= count,
            hearts + diamonds + high_card_points >= count,
            hearts + clubs + high_card_points >= count,
            diamonds + clubs + high_card_points >= count,
        )
    )

rule_of_twenty = _expr_for_point_rule(20)
rule_of_nineteen = _expr_for_point_rule(19)

# FIXME: This rule probably needs to consider min_hcp_for_open
rule_of_fifteen = z3.And(spades + high_card_points >= 15, high_card_points >= min_hcp_for_open, playing_points >= 12)

two_of_the_top_three_spades = ace_of_spades + king_of_spades + queen_of_spades >= 2
two_of_the_top_three_hearts = ace_of_hearts + king_of_hearts + queen_of_hearts >= 2
two_of_the_top_three_diamonds = ace_of_diamonds + king_of_diamonds + queen_of_diamonds >= 2
two_of_the_top_three_clubs = ace_of_clubs + king_of_clubs + queen_of_clubs >= 2

three_of_the_top_five_spades = ace_of_spades + king_of_spades + queen_of_spades + jack_of_spades + ten_of_spades >= 3
three_of_the_top_five_hearts = ace_of_hearts + king_of_hearts + queen_of_hearts + jack_of_hearts + ten_of_hearts >= 3
three_of_the_top_five_diamonds = ace_of_diamonds + king_of_diamonds + queen_of_diamonds + jack_of_diamonds + ten_of_diamonds >= 3
three_of_the_top_five_clubs = ace_of_clubs + king_of_clubs + queen_of_clubs + jack_of_clubs + ten_of_clubs >= 3

three_of_the_top_five_spades_or_better = z3.Or(two_of_the_top_three_spades, three_of_the_top_five_spades)
three_of_the_top_five_hearts_or_better = z3.Or(two_of_the_top_three_hearts, three_of_the_top_five_hearts)
three_of_the_top_five_diamonds_or_better = z3.Or(two_of_the_top_three_diamonds, three_of_the_top_five_diamonds)
three_of_the_top_five_clubs_or_better = z3.Or(two_of_the_top_three_clubs, three_of_the_top_five_clubs)

third_round_stopper_spades = z3.Or(ace_of_spades == 1, z3.And(king_of_spades == 1, spades >= 2), z3.And(queen_of_spades == 1, spades >= 3))
third_round_stopper_hearts = z3.Or(ace_of_hearts == 1, z3.And(king_of_hearts == 1, hearts >= 2), z3.And(queen_of_hearts == 1, hearts >= 3))
third_round_stopper_diamonds = z3.Or(ace_of_diamonds == 1, z3.And(king_of_diamonds == 1, diamonds >= 2), z3.And(queen_of_diamonds == 1, diamonds >= 3))
third_round_stopper_clubs = z3.Or(ace_of_clubs == 1, z3.And(king_of_clubs == 1, clubs >= 2), z3.And(queen_of_clubs == 1, clubs >= 3))

number_of_aces = ace_of_spades + ace_of_hearts + ace_of_diamonds + ace_of_clubs
number_of_kings = king_of_spades + king_of_hearts + king_of_diamonds + king_of_clubs

balanced = z3.And(doubletons <= 1, singletons == 0, voids == 0)

stopper_spades = z3.Or(ace_of_spades == 1, z3.And(king_of_spades == 1, spades >= 2), z3.And(queen_of_spades == 1, spades >= 3), z3.And(jack_of_spades == 1, ten_of_spades == 1, spades >= 4))
stopper_hearts = z3.Or(ace_of_hearts == 1, z3.And(king_of_hearts == 1, hearts >= 2), z3.And(queen_of_hearts == 1, hearts >= 3), z3.And(jack_of_hearts == 1, ten_of_hearts == 1, hearts >= 4))
stopper_diamonds = z3.Or(ace_of_diamonds == 1, z3.And(king_of_diamonds == 1, diamonds >= 2), z3.And(queen_of_diamonds == 1, diamonds >= 3), z3.And(jack_of_diamonds == 1, ten_of_diamonds == 1, diamonds >= 4))
stopper_clubs = z3.Or(ace_of_clubs == 1, z3.And(king_of_clubs == 1, clubs >= 2), z3.And(queen_of_clubs == 1, clubs >= 3), z3.And(jack_of_clubs == 1, ten_of_clubs == 1, clubs >= 4))

NO_CONSTRAINTS = z3.BoolVal(True)


def expr_for_suit(suit):
    return (clubs, diamonds, hearts, spades)[suit.index]


def stopper_expr_for_suit(suit):
    return (
        stopper_clubs,
        stopper_diamonds,
        stopper_hearts,
        stopper_spades,
    )[suit.index]


def support_points_expr_for_suit(suit):
    return (
        points_supporting_clubs,
        points_supporting_diamonds,
        points_supporting_hearts,
        points_supporting_spades,
    )[suit.index]


def expr_for_hand(hand):
    cards_in_spades = hand.cards_in_suit(suit.SPADES)
    cards_in_hearts = hand.cards_in_suit(suit.HEARTS)
    cards_in_diamonds = hand.cards_in_suit(suit.DIAMONDS)
    cards_in_clubs = hand.cards_in_suit(suit.CLUBS)

    return z3.And(
        spades == len(cards_in_spades),
        hearts == len(cards_in_hearts),
        diamonds == len(cards_in_diamonds),
        clubs == len(cards_in_clubs),

        ace_of_spades == int('A' in cards_in_spades),
        king_of_spades == int('K' in cards_in_spades),
        queen_of_spades == int('Q' in cards_in_spades),
        jack_of_spades == int('J' in cards_in_spades),
        ten_of_spades == int('T' in cards_in_spades),

        ace_of_hearts == int('A' in cards_in_hearts),
        king_of_hearts == int('K' in cards_in_hearts),
        queen_of_hearts == int('Q' in cards_in_hearts),
        jack_of_hearts == int('J' in cards_in_hearts),
        ten_of_hearts == int('T' in cards_in_hearts),

        ace_of_diamonds == int('A' in cards_in_diamonds),
        king_of_diamonds == int('K' in cards_in_diamonds),
        queen_of_diamonds == int('Q' in cards_in_diamonds),
        jack_of_diamonds == int('J' in cards_in_diamonds),
        ten_of_diamonds == int('T' in cards_in_diamonds),

        ace_of_clubs == int('A' in cards_in_clubs),
        king_of_clubs == int('K' in cards_in_clubs),
        queen_of_clubs == int('Q' in cards_in_clubs),
        jack_of_clubs == int('J' in cards_in_clubs),
        ten_of_clubs == int('T' in cards_in_clubs),
    )


positions = enum.Enum(
    "RHO",
    "Partner",
    "LHO",
    "Me",
)


def is_certain(solver, expr):
    solver.push()
    solver.add(z3.Not(expr))
    result = solver.check() == z3.unsat
    solver.pop()
    return result


def is_possible(solver, expr):
    solver.push()
    solver.add(expr)
    result = solver.check() == z3.sat
    solver.pop()
    return result
