# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.position import *
from core.call import Call
from suit import SUITS

import copy
import math
import operator


# I'm not sure this needs to be its own class.
class Vulnerability(object):
    def __init__(self, name):
        # FIXME: We should find a better storage system than strings.
        self.name = name or 'None'
        assert self.name in ('E-W', 'N-S', 'None', 'Both'), "%s is not a valid vulnerability" % self.name

    name_to_identifier = { 'E-W': 'EW', 'N-S': 'NS', 'None': 'NO', 'Both': 'BO' }
    identifier_to_name = dict([(identifier, name) for name, identifier in name_to_identifier.items()])

    @property
    def identifier(self):
        return self.name_to_identifier[self.name]

    @classmethod
    def from_identifier(cls, identifier):
        return Vulnerability(cls.identifier_to_name[identifier])

    @classmethod
    def from_string(cls, string):
        return Vulnerability(string)

    def gib_name(self):
        return { 'E-W': 'e', 'N-S': 'n', 'None': '-', 'Both': 'b' }[self.name]

    @classmethod
    def from_board_number(self, board_number):
        # http://www.jazclass.aust.com/bridge/scoring/score11.htm
        # FIXME: There must be a more compact way to represent this series.
        number_to_vulnerability = {
            0: 'E-W', # board 16
            1: 'None',
            2: 'N-S',
            3: 'E-W',
            4: 'Both',
            5: 'N-S',
            6: 'E-W',
            7: 'Both',
            8: 'None',
            9: 'E-W',
            10: 'Both',
            11: 'None',
            12: 'N-S',
            13: 'Both',
            14: 'None',
            15: 'N-S',
        }
        return Vulnerability(number_to_vulnerability[board_number % 16])

    def is_vulnerable(self, position):
        if self.name == "None":
            return False
        if self.name == "Both":
            return True
        return position.char in self.name


# FIXME: It's unclear if this class should expose just call_names or Call objects.
class CallHistory(object):
    @classmethod
    def _calls_from_calls_string(cls, calls_string):
        if not calls_string:
            return []
        if ',' in calls_string:
            calls_string = calls_string.replace(',', ' ')
        calls_string = calls_string.strip()  # Remove any trailing whitespace.
        call_names = calls_string.split(' ')
        # This if exists to support string == ''
        if not call_names or not call_names[0]:
            return []
        # from_string may be more forgiving than we want...
        calls = map(Call.from_string, call_names)
        assert None not in calls, "Failed to parse calls string: '%s'" % calls_string
        return calls

    @classmethod
    def from_string(cls, history_string, dealer_char=None, vulnerability_string=None):
        dealer = Position.from_char(dealer_char) if dealer_char else None
        vulnerability = Vulnerability.from_string(vulnerability_string)
        calls = cls._calls_from_calls_string(history_string)
        return CallHistory(calls, dealer=dealer, vulnerability=vulnerability)

    @classmethod
    def dealer_from_board_number(cls, board_number):
        # It's unclear if this number->dealer/vulnerability knowledge belongs in CallHistory or in Board.
        dealer_index = (board_number + 3) % 4
        return Position.from_index(dealer_index)

    @classmethod
    def from_board_number_and_calls_string(cls, board_number, calls_string):
        vulnerability = Vulnerability.from_board_number(board_number)
        dealer = cls.dealer_from_board_number(board_number)
        calls = cls._calls_from_calls_string(calls_string)
        return CallHistory(calls=calls, dealer=dealer, vulnerability=vulnerability)

    @classmethod
    def empty_for_board_number(cls, board_number):
        return cls.from_board_number_and_calls_string(board_number, '')

    def __init__(self, calls=None, dealer=None, vulnerability=None):
        self.calls = calls or []
        self.dealer = dealer or NORTH
        self.vulnerability = vulnerability or Vulnerability.from_board_number(1)

    def __str__(self):
        return "<CallHistory: %s>" % self.calls_string()

    def __len__(self):
        return len(self.calls)

    def can_double(self):
        # Make sure we haven't already doubled.
        if not self.last_non_pass().is_contract():
            return False
        return not self.declarer().in_partnership_with(self.position_to_call())

    def can_redouble(self):
        if not self.last_non_pass().is_double():
            return False
        return self.declarer().in_partnership_with(self.position_to_call())

    # This may belong on a separate bridge-rules object?
    def is_legal_call(self, call):
        assert not self.is_complete()
        if call.is_pass():
            return True
        last_contract = self.last_contract()
        if not last_contract:
            return not call.is_double() and not call.is_redouble()
        # Doubles do not have levels.
        if call.level:
            if last_contract.level > call.level:
                return False
            if last_contract.level == call.level and last_contract.strain >= call.strain:
                return False
        if call.is_double() and not self.can_double():
            return False
        if call.is_redouble() and not self.can_redouble():
            return False
        return True

    def copy_appending_call(self, call):
        assert call
        assert self.is_legal_call(call)
        new_call_history = copy.deepcopy(self)
        new_call_history.calls.append(call)
        return new_call_history

    def copy_with_partial_history(self, last_entry):
        partial_history = copy.copy(self)
        partial_history.calls = self.calls[:last_entry]
        return partial_history

    def ascending_partial_histories(self, step):
        partial_histories = []
        partial_history = self
        while partial_history.calls:  # We only terminate from here if passed in an empty history.
            partial_histories.insert(0, partial_history)
            if len(partial_history.calls) < step:
                break
            partial_history = partial_history.copy_with_partial_history(-step)
        return partial_histories

    @property
    def identifier(self):
        return "%s:%s:%s" % (self.dealer.char, self.vulnerability.identifier, self.comma_separated_calls())

    @classmethod
    def from_identifier(cls, identifier):
        components = identifier.split(":")
        if len(components) == 3:
            dealer_char, vulenerability_identifier, calls_identifier = components
        elif len(components) == 2:
            # It's very common to have the last colon in the URL missing.
            dealer_char, vulenerability_identifier = components
            calls_identifier = ""
        else:
            assert False, "Invalid history identifier: %s" % identifier

        dealer = Position.from_char(dealer_char)
        vulnerability = Vulnerability.from_identifier(vulenerability_identifier)
        calls = cls._calls_from_calls_string(calls_identifier)
        return CallHistory(calls=calls, dealer=dealer, vulnerability=vulnerability)

    def pretty_one_line(self):
        return "Deal: %s, Bids: %s" % (self.dealer.char, self.calls_string())

    def calls_string(self):
        return " ".join([call.name for call in self.calls])

    def comma_separated_calls(self):
        return ",".join([call.name for call in self.calls])

    @property
    def last_call(self):
        if not self.calls:
            return None
        return self.calls[-1]

    @property
    def last_to_call(self):
        if not self.calls:
            return None
        return self.dealer.position_after_n_calls(len(self.calls) - 1)

    def last_non_pass(self):
        for call in reversed(self.calls):
            if not call.is_pass():
                return call
        return None

    def last_to_not_pass(self):
        for callder, call in self.enumerate_reversed_calls():
            if not call.is_pass():
                return callder
        return None

    def last_contract(self):
        for call in reversed(self.calls):
            if call.is_contract():
                return call
        return None

    def position_to_call(self):
        # FIXME: Should this return None when is_complete?
        # We'd have to check callers, some may assume it's OK to call position_to_call after is_complete.
        return self.dealer.position_after_n_calls(len(self.calls))

    def calls_by(self, position):
        offset_from_dealer = self.dealer.calls_between(position)
        if len(self.calls) <= offset_from_dealer:
            return []
        return [self.calls[i] for i in range(offset_from_dealer, len(self.calls), 4)]

    def enumerate_calls(self):
        for call_offset, call in enumerate(self.calls):
            yield self.dealer.position_after_n_calls(call_offset), call

    def enumerate_reversed_calls(self):
        # FIXME: This is needlessly complicated.
        for call_offset, call in enumerate(reversed(self.calls)):
            caller_offset = len(self.calls) - 1 - call_offset
            yield self.dealer.position_after_n_calls(caller_offset), call

    def competative_auction(self):
        first_caller = None
        for caller, call in self.enumerate_calls():
            if not first_caller and call.is_contract():
                first_caller = caller
            if call.is_contract() and not caller.in_partnership_with(first_caller):
                return True
        return False

    def last_call_by(self, position):
        calls =  self.calls_by(position)
        if not calls:
            return None
        return calls[-1]

    def first_call_by(self, position):
        calls =  self.calls_by(position)
        if not calls:
            return None
        return calls[0]

    def last_call_by_next_bidder(self):
        next_caller = self.position_to_call()
        return self.last_call_by(next_caller)

    def opener(self):
        for caller, call in self.enumerate_calls():
            if call.is_contract():
                return caller
        return None

    def declarer(self):
        first_caller = None
        first_call = None
        last_caller = None
        last_call = None
        for caller, call in self.enumerate_reversed_calls():
            if not call.is_contract():
                continue
            if not last_call:
                last_call = call
                last_caller = caller
            if call.strain == last_call.strain and caller.in_partnership_with(last_caller):
                first_call = call
                first_caller = caller
        return first_caller

    def dummy(self):
        return declarer.partner

    def contract(self):
        # Maybe we need a Contract object which holds declarer, suit, level, and doubles?
        last_contract = self.last_contract()
        if last_contract:
            last_non_pass = self.last_non_pass()
            double_string = ''
            if last_non_pass.is_double():
                double_string = 'X'
            elif last_non_pass.is_redouble():
                double_string = 'XX'
            return "%s%s" % (last_contract.name, double_string)
        return None

    def is_complete(self):
        return len(self.calls) > 3 and self.calls[-1].is_pass() and self.calls[-2].is_pass() and self.calls[-3].is_pass()

    def is_passout(self):
        return self.is_complete() and self.calls[-4].is_pass()
