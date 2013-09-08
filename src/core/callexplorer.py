# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import copy

from core.call import Call
from core.callhistory import CallHistory
from core.suit import *


class CallExplorer(object):
    def possible_calls_over(self, history):
        if history.is_complete():
            return

        yield Call('P')

        last_non_pass = history.last_non_pass()
        caller = history.position_to_call()
        if last_non_pass and history.last_to_not_pass() != caller.partner:
            if last_non_pass.is_contract():
                yield Call('X')
            elif last_non_pass.is_double():
                yield Call('XX')

        last_contract = history.last_contract()
        for level in range(1, 8):
            if last_contract and level < last_contract.level:
                continue
            for strain in STRAINS:
                if last_contract and level == last_contract.level and strain <= last_contract.strain:
                    continue
                yield Call.from_level_and_strain(level, strain)

    def possible_futures(self, history):
        future_history = copy.copy(history)
        for call in self.possible_calls_over(history):
            future_history.calls.append(call)
            yield future_history
            future_history.calls.pop()

    def _split_before_last_token(self, string, delimeter=" "):
        last_delimiter_index = string.rfind(delimeter)
        if last_delimiter_index == -1:
            return "", string
        return string[:last_delimiter_index], string[last_delimiter_index + 1:]

    def _has_wildcards(self, string):
        return "*" in string

    def _match_pattern_over(self, history, pattern):
        # FIXME: We could support fancier pattern matching.
        assert pattern == "*"
        for call in self.possible_calls_over(history):
            yield call

    def _glob_helper(self, history, call_name):
        call = Call.from_string(call_name)
        # call_name can be empty if the original string is emtpy or there is trailing whitespace.
        if call and history.is_legal_call(call):
            yield call

    # FIXME: Unclear if history_iglob should be so tolerant.
    def _normalize_glob_string(self, glob_string):
        # Leading/trailing whitespace will confuse our algorithm.
        return glob_string.replace(",", " ").replace("  ", " ").strip()

    def history_iglob(self, glob_string):
        glob_string = self._normalize_glob_string(glob_string)
        glob_string, last_token = self._split_before_last_token(glob_string)
        histories = self.history_iglob(glob_string) if self._has_wildcards(glob_string) else [CallHistory.from_string(glob_string)]
        call_generator = self._match_pattern_over if self._has_wildcards(last_token) else self._glob_helper

        for history in histories:
            # If we already have 3 passes in a row, there is nothing more we an add to this history.
            if history.is_complete():
                continue
            for call in call_generator(history, last_token):
                yield history.copy_appending_call(call)

    def history_glob(self, glob_string):
        return list(self.history_iglob(glob_string))
