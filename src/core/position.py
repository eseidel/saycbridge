# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from third_party.memoized import memoized


def position_name(position):
	return position.name

def position_from_name(name):
	return Postion.from_name(name)

def position_char(position):
	return position.char

def position_from_char(char):
	return Position.from_char(char)

def partner_of(position):
	return position.partner

def rho_of(position):
	return position.rho

def lho_of(position):
	return position.rho

def in_partnership_with(position, other_position):
	return position.in_partnership_with(other_position)


class Position(object):
	def __init__(self, index, this_should_not_be_called_directly=False):
		assert(this_should_not_be_called_directly)
		self.index = index

	@classmethod
	@memoized
	def from_index(cls, index):
		assert index in range(4)
		return cls(index, this_should_not_be_called_directly=True)

	@classmethod
	def from_name(cls, name):
		index = ('North','East','South','West').index(char)
		return cls.from_index(index)

	@classmethod
	def from_char(cls, char):
		index = ('N','E','S','W').index(char)
		return cls.from_index(index)

	@property
	def name(self):
		return ("North", "East", "South", "West")[self.index]

	@property
	def char(self):
		return self.name[0]

	@property
	def lho(self):
		return self.position_after_n_calls(1)

	@property
	def partner(self):
		return self.position_after_n_calls(2)

	@property
	def rho(self):
		return self.position_after_n_calls(3)

	def in_partnership_with(self, position):
		return position == self or position == self.partner

	def position_after_n_calls(self, offset):
		other_index = (self.index + offset) % 4
		return Position.from_index(other_index)

	def calls_between(self, other):
		return (other.index - self.index) % 4


NORTH, EAST, SOUTH, WEST = map(Position.from_index, range(4))
POSITIONS = [NORTH, EAST, SOUTH, WEST]
