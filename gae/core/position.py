# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

POSITIONS = range(4)
NORTH, EAST, SOUTH, WEST = range(4)

def position_name(position):
    return ("North", "East", "South", "West")[position]

def position_from_name(position_name):
    return ["North", "East", "South", "West"].index(position_name)

def position_char(position):
    return ("N", "E", "S", "W")[position]

def position_from_char(char):
    # tuples don't have an index method in python 2.5 (on appengine)
    return ["N", "E", "S", "W"].index(char)

def partner_of(position):
    return (position + 2) % 4

# right_hand_opponent
def rho_of(position):
    return (position - 1) % 4

# left_hand_opponent
def lho_of(position):
    return (position - 3) % 4

def in_partnership_with(position, other_position):
    return position == other_position or position == partner_of(other_position)
