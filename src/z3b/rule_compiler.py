# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.call import Call
from itertools import chain
from third_party.memoized import memoized
from z3b import enum
from z3b import model
from z3b import ordering
from z3b.constraints import Constraint
from z3b.preconditions import implies_artificial, annotations
import z3


categories = enum.Enum(
    "Relay",
    "Gadget",
    "NotrumpSystem",
    "Default",
    "Natural",
    "LawOfTotalTricks",
    "NaturalPass",
    "DefaultPass",
)

# This class exists so that we can add asserts specific to how how orderings work for saycbridge.
class RuleOrdering(object):
    def __init__(self):
        self.ordering = ordering.Ordering()

    def _check_key(self, key):
        assert not hasattr(key, '__dict__') or not ('priority' in key.__dict__), "%s has a priority property and is being used as a priority" % key
        return key

    def order(self, *args):
        return self.ordering.order(*map(self._check_key, args))

    def lt(self, left, right):
        try:
            return self.ordering.lt(left, right)
        except TypeError, e:
            print "Exception during lt(%s, %s)" % (left, right)
            raise


rule_order = RuleOrdering()


# FIXME: We should integrate this function into RuleOrdering.
def all_priorities_for_rule(dsl_rule):
    compiled_rule = RuleCompiler.compile(dsl_rule)
    return compiled_rule.all_priorities


# This is a public interface from DSL Rules to the rest of the system.
class CompiledRule(object):
    def __init__(self, rule, preconditions, known_calls, shared_constraints, annotations, constraints, default_priority, conditional_priorities_per_call, priorities_per_call):
        self.dsl_rule = rule
        self.preconditions = preconditions
        self.known_calls = known_calls
        self.shared_constraints = shared_constraints
        self._annotations = annotations
        self.constraints = constraints
        self.default_priority = default_priority
        self.conditional_priorities_per_call = conditional_priorities_per_call
        self.priorities_per_call = priorities_per_call
        # FIXME: Should forcing be an annotation instead?  It has an awkward tri-state currently.
        self.forcing = self.dsl_rule.forcing

    @property
    def all_priorities(self):
        conditional_priorities = [priority for _, priority in self.conditional_priorities_per_call.values()]
        return set([self.default_priority] + self.priorities_per_call.values() + conditional_priorities)

    @property
    def requires_planning(self):
        return self.dsl_rule.requires_planning

    def annotations_for_call(self, call):
        if self.dsl_rule.annotations_per_call:
            per_call_annotations = self.dsl_rule.annotations_per_call.get(call.name)
            if per_call_annotations:
                return self._annotations | set(RuleCompiler._ensure_list(per_call_annotations))
        return self._annotations

    @property
    def name(self):
        return self.dsl_rule.name()

    def __str__(self):
        return self.name

    def __repr__(self):
        # List printing looks nicer if we lie here.
        return self.dsl_rule.name()

    # FIXME: This exists for compatiblity with KBB's Rule interface and is used by autobid_handler.py
    def explanation_for_bid(self, call):
        explanation = self.dsl_rule.explanations_per_call.get(call.name)
        if explanation:
            return explanation
        return self.dsl_rule.explanation

    def _fits_preconditions(self, history, call, expected_call=None):
        try:
            for precondition in self.preconditions:
                if not precondition.fits(history, call):
                    if call == expected_call and expected_call in self.known_calls:
                        print " %s failed: %s" % (self, precondition)
                    return False
        except Exception, e:
            print "Exception evaluating preconditions for %s" % self.name
            raise
        return True

    def calls_over(self, history, expected_call=None):
        for call in history.legal_calls.intersection(self.known_calls):
            if self._fits_preconditions(history, call, expected_call):
                yield self.dsl_rule.category, call

    def _constraint_exprs_for_call(self, history, call):
        exprs = []
        per_call_constraints, _ = self.per_call_constraints_and_priority(history, call)
        if per_call_constraints:
            exprs.extend(RuleCompiler.exprs_from_constraints(per_call_constraints, history, call))
        exprs.extend(RuleCompiler.exprs_from_constraints(self.shared_constraints, history, call))
        return exprs

    def meaning_of(self, history, call):
        try:
            exprs = self._constraint_exprs_for_call(history, call)
            per_call_conditionals = self.conditional_priorities_per_call.get(call.name)
            if per_call_conditionals:
                for condition, priority in per_call_conditionals:
                    condition_exprs = RuleCompiler.exprs_from_constraints(condition, history, call)
                    yield priority, z3.And(exprs + condition_exprs)

            for condition, priority in self.dsl_rule.conditional_priorities:
                condition_exprs = RuleCompiler.exprs_from_constraints(condition, history, call)
                yield priority, z3.And(exprs + condition_exprs)

            _, priority = self.per_call_constraints_and_priority(history, call)
            assert priority
            yield priority, z3.And(exprs)
        except:
            print "Exception compiling meaning_of %s over %s with %s" % (call, history.call_history.calls_string(), self)
            raise

    # constraints accepts various forms including:
    # constraints = { '1H': hearts > 5 }
    # constraints = { '1H': (hearts > 5, priority) }
    # constraints = { ('1H', '2H'): hearts > 5 }

    # FIXME: Should we split this into two methods? on for priority and one for constraints?
    def per_call_constraints_and_priority(self, history, call):
        constraints_tuple = self.constraints.get(call.name)
        try:
            list(constraints_tuple)
        except TypeError:
            priority = self.priorities_per_call.get(call.name, self.default_priority)
            constraints_tuple = (constraints_tuple, priority)
        assert len(constraints_tuple) == 2
        # FIXME: Is it possible to not end up with a priority anymore?
        assert constraints_tuple[1], "" + self.name + " is missing priority"
        return constraints_tuple


class RuleCompiler(object):
    @classmethod
    def exprs_from_constraints(cls, constraints, history, call):
        if not constraints:
            return [model.NO_CONSTRAINTS]

        if isinstance(constraints, Constraint):
            return [constraints.expr(history, call)]

        if isinstance(constraints, z3.ExprRef):
            return [constraints]

        return chain.from_iterable([cls.exprs_from_constraints(constraint, history, call) for constraint in constraints])

    @classmethod
    def _collect_from_ancestors(cls, dsl_class, property_name):
        getter = lambda ancestor: getattr(ancestor, property_name, [])
        # The DSL expects that parent preconditions, etc. apply before child ones.
        return map(getter, reversed(dsl_class.__mro__))

    @classmethod
    def _ensure_list(cls, value_or_list):
        if value_or_list and not hasattr(value_or_list, '__iter__'):
            return [value_or_list]
        return value_or_list

    @classmethod
    def _joined_list_from_ancestors(cls, dsl_class, property_name):
        values_from_ancestors = cls._collect_from_ancestors(dsl_class, property_name)
        mapped_values = map(cls._ensure_list, values_from_ancestors)
        return list(chain.from_iterable(mapped_values))

    @classmethod
    def _compile_known_calls(cls, dsl_class, constraints, priorities_per_call):
        if dsl_class.call_names:
            call_names = cls._ensure_list(dsl_class.call_names)
        elif priorities_per_call:
            call_names = priorities_per_call.keys()
            assert dsl_class.shared_constraints or priorities_per_call.keys() == constraints.keys()
        else:
            call_names = constraints.keys()
        assert call_names, "%s: call_names or priorities_per_call or constraints map is required." % dsl_class.__name__
        return map(Call.from_string, call_names)

    @classmethod
    def _flatten_tuple_keyed_dict(cls, original_dict):
        flattened_dict  = {}
        for tuple_key, value in original_dict.iteritems():
            if hasattr(tuple_key, '__iter__'):
                for key in tuple_key:
                    assert key not in flattened_dict, "Key (%s) was listed twice in %s" % (key, original_dict)
                    flattened_dict[key] = value
            else:
                assert tuple_key not in flattened_dict, "Key (%s) was listed twice in %s" % (tuple_key, original_dict)
                flattened_dict[tuple_key] = value
        return flattened_dict

    @classmethod
    def _compile_annotations(cls, dsl_class):
        compiled_set = set(cls._joined_list_from_ancestors(dsl_class, 'annotations'))
        # FIXME: We should probably assert that no more than one of the "implies_artificial"
        # annotations are in this set at once.  Those all have distinct meanings.
        if implies_artificial.intersection(compiled_set):
            compiled_set.add(annotations.Artificial)
        return compiled_set

    @classmethod
    def _validate_rule(cls, dsl_class):
        # Rules have to apply some constraints to the hand.
        assert dsl_class.constraints or dsl_class.shared_constraints, "" + dsl_class.name() + " is missing constraints"
        # conditional_priorities doesn't work with self.constraints
        assert not dsl_class.conditional_priorities or not dsl_class.constraints
        assert not dsl_class.conditional_priorities or dsl_class.call_names
        properties = dsl_class.__dict__.keys()
        public_properties = filter(lambda p: not p.startswith("_"), properties)
        unexpected_properties = set(public_properties) - Rule.ALLOWED_KEYS
        assert not unexpected_properties, "%s defines unexpected properties: %s" % (dsl_class, unexpected_properties)

    @classmethod
    def _default_priority(cls, dsl_rule):
        if dsl_rule.priority:
            return dsl_rule.priority
        return dsl_rule # Use the class as the default priority.

    @classmethod
    @memoized
    def compile(cls, dsl_rule):
        try:
            cls._validate_rule(dsl_rule)
            constraints = cls._flatten_tuple_keyed_dict(dsl_rule.constraints)
            priorities_per_call = cls._flatten_tuple_keyed_dict(dsl_rule.priorities_per_call)
            # Unclear if compiled results should be memoized on the rule?
            return CompiledRule(dsl_rule,
                known_calls=cls._compile_known_calls(dsl_rule, constraints, priorities_per_call),
                annotations=cls._compile_annotations(dsl_rule),
                preconditions=cls._joined_list_from_ancestors(dsl_rule, 'preconditions'),
                shared_constraints=cls._joined_list_from_ancestors(dsl_rule, 'shared_constraints'),
                constraints=constraints,
                default_priority=cls._default_priority(dsl_rule),
                conditional_priorities_per_call=cls._flatten_tuple_keyed_dict(dsl_rule.conditional_priorities_per_call),
                priorities_per_call=priorities_per_call,
            )
        except:
            print "Exception compiling %s" % dsl_rule
            raise


# The rules of SAYC are all described in terms of Rule.
# These classes exist to support the DSL and make it easy to concisely express
# the conventions of SAYC.
class Rule(object):
    # All properties with [] (empty list) defaults, auto-collect
    # from parent classes.  foo = Parent.foo + [bar] is never necessary in this DSL.
    annotations = []
    annotations_per_call = {} # { '1C' : (annotations.Foo, annotations.Bar) }
    call_names = None # For when all calls share the same constraints
    category = categories.Default # Intra-bid priority
    conditional_priorities = [] # e.g. [(condition, priority), (condition, priority)]
    conditional_priorities_per_call = {} # e.g. {'1C': [(condition, priority), (condition, priority)]}
    constraints = {} # { '1C' : constraints, '1D': (constraints, priority), '1H' : constraints }
    forcing = None
    preconditions = []
    priorities_per_call = {} # { '1C': priority, '1D': another_priority }
    priority = None # Defaults to the class if None.
    requires_planning = False
    shared_constraints = [] # constraints which apply to call possible call_names.
    explanations_per_call = {}
    explanation = None

    # These are the only properties which are allowed to be defined in subclasses.
    # The RuleCompiler with enforce this.
    # FIXME: Should we autogenerate this list from this Rule declaration?
    ALLOWED_KEYS = set([
        "annotations",
        "annotations_per_call",
        "call_names",
        "category",
        "conditional_priorities",
        "conditional_priorities_per_call",
        "constraints",
        "forcing",
        "preconditions",
        "priorities_per_call",
        "priority",
        "requires_planning",
        "shared_constraints",
        "explanations_per_call",
        "explanation",
    ])

    def __init__(self):
        assert False, "Rule objects should be compiled into EngineRule objects instead of instantiating them."

    @classmethod
    def name(cls):
        return cls.__name__

    def __repr__(self):
        return "%s()" % self.name
