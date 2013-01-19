import copy

from core.call import Call
from core.callhistory import CallHistory
from core.position import partner_of
from core.suit import *


class CallExplorer(object):
    def _make_call(self, level, strain):
        return Call("%s%s" % (level, strain_char(strain)))

    def possible_calls_over(self, history):
        if history.is_complete():
            return

        yield Call('P')

        last_non_pass = history.last_non_pass()
        caller = history.position_to_call()
        if last_non_pass and history.last_to_not_pass() != partner_of(caller):
            if last_non_pass.is_contract():
                yield Call('X')
            elif last_non_pass.is_double():
                yield Call('XX')

        last_contract = history.last_contract()
        for level in range(1, 8):
            if last_contract and level < last_contract.level():
                continue
            for strain in STRAINS:
                if last_contract and level == last_contract.level() and strain <= last_contract.strain:
                    continue
                yield self._make_call(level, strain)

    def possible_futures(self, history):
        future_history = copy.copy(history)
        for call in self.possible_calls_over(history):
            future_history.calls.append(call)
            yield future_history
            future_history.calls.pop()
