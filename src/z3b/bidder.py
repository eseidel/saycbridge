# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.call import Call
from core.callexplorer import CallExplorer
from core.callhistory import CallHistory
from itertools import chain
from third_party import enum
from third_party.memoized import memoized
from z3b.model import positions, expr_for_suit, is_possible
import copy
import z3
import z3b.model as model
import z3b.rules as rules


class SolverPool(object):
    def create_solver(self):
        solver = z3.SolverFor('QF_LIA')
        solver.add(model.axioms)
        return solver

    @memoized
    def solver_for_hand(self, hand):
        solver = self.create_solver()
        solver.add(model.expr_for_hand(hand))
        return solver


_solver_pool = SolverPool()


# Intra-bid priorities, first phase, "interpretation priorities", like "natural, conventional" (possibly should be called types?) These select which "1N" meaning is correct.
# Inter-bid priorities, "which do you look at first" -- these order preference between "1H, vs. 1S"
# Tie-breaker-priorities -- planner stage, when 2 bids match which we make.


# The dream:
# history.my.solver
# annotations.Opening in history.rho.annotations
# annotations.Opening in history.rho.last_call.annotations
# history.partner.min_length(suit)
# history.partner.max_length(suit)
# history.partner.min_hcp()
# history.partner.max_hcp()


class PositionView(object):
    def __init__(self, history, position):
        self.history = history
        self.position = position

    @property
    def annotations(self):
        return self.history.annotations_for_position(self.position)

    @property
    def last_call(self):
        return self.history.last_call_for_position(self.position)

    # FIXME: We could hang annotations off of the Call object, but currently
    # Call is from the old system.
    @property
    def annotations_for_last_call(self):
        return self.history.annotations_for_last_call(self.position)

    @property
    def min_points(self):
        return self.history.min_points_for_position(self.position)

    def min_length(self, suit):
        return self.history.min_length_for_position(self.position, suit)


# This class is immutable.
class History(object):
    def __init__(self, previous_history=None, call=None, annotations=None, constraints=None):
        self._previous_history = previous_history
        self._annotations_for_last_call = annotations if annotations else []
        self._constraints_for_last_call = constraints if constraints else []
        self.call_history = copy.deepcopy(self._previous_history.call_history) if self._previous_history else CallHistory()
        if call:
            self.call_history.calls.append(call)

    def extend_with(self, call, annotations, constraints):
        return History(
            previous_history=self,
            call=call,
            annotations=annotations,
            constraints=constraints,
        )

    def _previous_position(self, position):
        return positions[(position.index - 1) % 4]

    def _history_after_last_call_for(self, position):
        if position == positions.RHO:
            return self
        if not self._previous_history:
            return None
        return self._previous_history._history_after_last_call_for(self._previous_position(position))

    @memoized
    def _solver_for_position(self, position):
        if not self._previous_history:
            return _solver_pool.create_solver()
        if position == positions.RHO:
            # The RHO just made a call, so we need to add the constraints from
            # that caller to that player's solver.
            previous_position = self._previous_position(position)
            solver = self._previous_history._solver_for_position.take(previous_position)
            solver.add(self._constraints_for_last_call)
            return solver
        history = self._history_after_last_call_for(position)
        if not history:
            return _solver_pool.create_solver()
        return history._solver

    @property
    def _solver(self):
        return self._solver_for_position(positions.RHO)

    @property
    def _four_calls_ago(self):
        history = (
            self._previous_history and
            self._previous_history._previous_history and
            self._previous_history._previous_history._previous_history and
            self._previous_history._previous_history._previous_history._previous_history
        )
        if not history:
            return None
        return history

    def _walk_history_for(self, position):
        history = self._history_after_last_call_for(position)
        while history:
            yield history
            history = history._four_calls_ago

    def _walk_annotations_for(self, position):
        for history in self._walk_history_for(position):
            yield history._annotations_for_last_call

    def annotations_for_last_call(self, position):
        history = self._history_after_last_call_for(position)
        if not history:
            return []
        return history._annotations_for_last_call

    def last_call_for_position(self, position):
        history = self._history_after_last_call_for(position)
        if not history:
            return None
        return history.call_history.last_call()

    def annotations_for_position(self, position):
        return chain.from_iterable(self._walk_annotations_for(position))

    def _walk_history(self):
        history = self
        while history:
            yield history
            history = history._previous_history

    def _walk_annotations(self):
        for history in self._walk_history():
            yield history._annotations_for_last_call

    @property
    def annotations(self):
        return chain.from_iterable(self._walk_annotations())

    @memoized
    def min_length_for_position(self, position, suit):
        history = self._history_after_last_call_for(position)
        if history:
            solver = history._solver
            suit_expr = expr_for_suit(suit)
            for length in range(0, 13):
                if is_possible(solver, suit_expr == length):
                    return length
        return 0

    @memoized
    def min_points_for_position(self, position):
        history = self._history_after_last_call_for(position)
        if history:
            solver = history._solver
            for pts in range(0, 37):
                if is_possible(solver, model.points == pts):
                    return pts
        return 0

    @memoized
    def is_unbid_suit(self, suit):
        suit_expr = expr_for_suit(suit)
        for position in positions:
            solver = self._solver_for_position(position)
            if not is_possible(solver, suit_expr < 3):
                return False
        return True

    @property
    def rho(self):
        return PositionView(self, positions.RHO)

    @property
    def me(self):
        return PositionView(self, positions.Me)

    @property
    def partner(self):
        return PositionView(self, positions.Partner)

    @property
    def lho(self):
        return PositionView(self, positions.LHO)

    def view_for(self, position):
        return PositionView(self, position)


class PossibleCalls(object):
    def __init__(self, ordering):
        self.ordering = ordering
        self._calls_and_priorities = []

    def add_call_with_priority(self, call, priority):
        self._calls_and_priorities.append([call, priority])

    def _is_dominated(self, priority, maximal_calls_and_priorities):
        # First check to see if any existing call is larger than this one.
        for max_call, max_priority in maximal_calls_and_priorities:
            if self.ordering.less_than(priority, max_priority):
                return True
        return False

    def calls_of_maximal_priority(self):
        maximal_calls_and_priorities = []
        for call, priority in self._calls_and_priorities:
            if self._is_dominated(priority, maximal_calls_and_priorities):
                continue
            maximal_calls_and_priorities = filter(lambda (max_call, max_priority): not self.ordering.less_than(max_priority, priority), maximal_calls_and_priorities)
            maximal_calls_and_priorities.append([call, priority])
        return [call for call, _ in maximal_calls_and_priorities]


class Bidder(object):
    def __init__(self):
        # Assuming SAYC for all sides.
        self.system = rules.StandardAmericanYellowCard

    def find_call_for(self, hand, call_history):
        history = Interpreter().create_history(call_history)
        # Select highest-intra-bid-priority (category) rules for all possible bids
        rule_selector = RuleSelector(self.system, history)
        # Compute inter-bid priorities (priority) for each using the hand.
        possible_calls = rule_selector.possible_calls_for_hand(hand)
        # The resulting priorities are only partially ordered, so have to be walked in a tree.
        maximal_calls = possible_calls.calls_of_maximal_priority()
        # Currently we have no tie-breaking priorities (no planner), so we just select the first call we found.
        maximal_calls = filter(lambda call: not rule_selector.rule_for_call(call).requires_planning, maximal_calls)
        if not maximal_calls:
            # If we failed to find a single maximal bid, this is an error.
            return None
        if len(maximal_calls) != 1:
            print "WARNING: Multiple bids match and have maximal tie-breaker priority"
            return None
        return maximal_calls[0]


class RuleSelector(object):
    def __init__(self, system, history):
        self.system = system
        self.history = history

    @property
    @memoized
    def _call_to_rule(self):
        maximal = {}
        for rule in self.system.rules:
            for category, call in rule.calls_over(self.history):
                current = maximal.get(call)
                if not current:
                    maximal[call] = (category, [rule])
                else:
                    existing_category, existing_rules = current

                    # FIXME: It's lame that enum's < is backwards.
                    if category < existing_category:
                        maximal[call] = (category, [rule])
                    elif category == existing_category:
                        existing_rules.append(rule)

        result = {}
        for call, best in maximal.iteritems():
            _, rules = best
            if len(rules) > 1:
                print "WARNING: Multiple bids have maximal category"
            result[call] = rules[0]
        return result

    def rule_for_call(self, call):
        return self._call_to_rule.get(call)

    @memoized
    def constraints_for_call(self, call):
        # Example:
        # (z3.Or(clubs > diamonds, clubs == diamonds == 3) AND !(ROT AND hearts >= 5) AND !(ROT AND spades >= 5))
        # OR
        # (!z3.Or(clubs > diamonds, clubs == diamonds == 3) AND !(ROT AND diamonds >=3) AND !(ROT AND hearts >= 5) AND !(ROT AND spades >= 5))

        situations = []
        rule = self.rule_for_call(call)
        for priority, z3_meaning in rule.meaning_of(self.history, call):
            situational_exprs = [z3_meaning]
            for unmade_call, unmade_rule in self._call_to_rule.iteritems():
                for unmade_priority, unmade_z3_meaning in unmade_rule.meaning_of(self.history, unmade_call):
                    # FIXME: < means > for priority compares.
                    if unmade_priority < priority:
                        situational_exprs.append(z3.Not(unmade_z3_meaning))
            situations.append(z3.And(situational_exprs))
        return z3.Or(situations)

    def possible_calls_for_hand(self, hand):
        possible_calls = PossibleCalls(self.system.priority_ordering)
        solver = _solver_pool.solver_for_hand(hand)
        for call in CallExplorer().possible_calls_over(self.history.call_history):
            rule = self.rule_for_call(call)
            if not rule:
                continue
            priority = rule.priority_for_call_and_hand(solver, self.history, call, hand)
            if not priority:
                continue
            possible_calls.add_call_with_priority(call, priority)
        return possible_calls


class Interpreter(object):
    def __init__(self):
        # Assuming SAYC for all sides.
        self.system = rules.StandardAmericanYellowCard

    def create_history(self, call_history):
        history = History()
        viewer = call_history.position_to_call()

        for partial_history in call_history.ascending_partial_histories(step=1):
            selector = RuleSelector(self.system, history)

            call = partial_history.last_call()
            rule = selector.rule_for_call(call)
            # We can interpret bids we know how to make.
            constraints = model.NO_CONSTRAINTS
            annotations = []
            if rule:
                annotations = rule.annotations
                constraints = selector.constraints_for_call(call)
                # FIXME: We should validate the new constraints before saving them in the knowledge.
            history = history.extend_with(call, annotations, constraints)

        return history

