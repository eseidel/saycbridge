from z3 import *
from third_party import enum
from core.callhistory import CallHistory
from core.call import Call
from core.hand import Hand
from core.callexplorer import CallExplorer
import core.suit as suit
from itertools import chain
import copy


spades, hearts, diamonds, clubs, points = Ints('spades hearts diamonds clubs points')

axioms = [
    spades + hearts + diamonds + clubs == 13,
    spades >= 0,
    hearts >= 0,
    diamonds >= 0,
    clubs >= 0,
    0 <= points <= 37,
]

rule_of_twenty = Or(
    spades + hearts + points >= 20,
    spades + diamonds + points >= 20,
    spades + clubs + points >= 20,
    hearts + diamonds + points >= 20,
    hearts + clubs + points >= 20,
    diamonds + clubs + points >= 20)

rule_of_nineteen = Or(
    spades + hearts + points >= 19,
    spades + diamonds + points >= 19,
    spades + clubs + points >= 19,
    hearts + diamonds + points >= 19,
    hearts + clubs + points >= 19,
    diamonds + clubs + points >= 19)

rule_of_fifteen = spades + points >= 15

# Intra-bid priorities, first phase, "interpretation priorities", like "natural, conventional" (possibly should be called types?) These select which "1N" meaning is correct.
# Inter-bid priorities, "which do you look at first" -- these order preference between "1H, vs. 1S"
# Tie-breaker-priorities -- planner stage, when 2 bids match which we make.

positions = enum.Enum(
    "RHO",
    "Partner",
    "LHO",
    "Me",
)


annotations = enum.Enum(
    "Opening",
)


class Precondition(object):
    def __repr__(self):
        return "%s()" % self.name()

    def name(self):
        return self.__class__.__name__

    def fits(self, history, call):
        pass


class NoOpening(Precondition):
    def fits(self, history, call):
        return annotations.Opening not in history.annotations


class Opened(Precondition):
    def __init__(self, position):
        self.position = position

    def fits(self, history, call):
        return annotations.Opening in history.annotations_for_position(self.position)


class Rule(object):
    preconditions = []
    category = None # Intra-bid priority

    call_name = None # FIXME: We will likely support more than one call per rule eventually.
    constraints = None
    annotations = []
    conditional_priorities = []
    priority = None

    def create_call(self, history):
        # FIXME: kbb rules can make more than one type of call, it's unclear
        # if we should follow that model here or not.
        call = Call(self.call_name)
        for precondition in self.preconditions:
            if not precondition.fits(history, call):
                return None
        return call

    def possible_priorities_and_conditions_for_call(self, call):
        # We're eventually going to allow more than one call per rule.
        assert call.name == self.call_name, self.call_name
        for condition, priority in self.conditional_priorities:
            yield priority, condition
        yield self.priority, BoolVal(True)

    def priority_for_call_and_hand(self, call, hand):
        solver = Solver()
        solver.add(axioms)
        solver.add(self.constraints)
        solver.add(expr_from_hand(hand))
        if solver.check() != sat:
            return None

        for condition, priority in self.conditional_priorities:
            solver.push()
            solver.add(condition)
            if solver.check() != sat:
                return priority
            solver.pop()
        return self.priority


opening_priorities = enum.Enum(
    "LongestMajor",
    "HigherMajor",
    "LowerMajor",
    "LongestMinor",
    "HigherMinor",
    "LowerMinor",
)


class Opening(Rule):
    annotations = [annotations.Opening]
    preconditions = [NoOpening()]


# FIXME: This is preconditioned on no-one having opened.
class OneClubOpening(Opening):
    call_name = '1C'
    constraints = And(rule_of_twenty, clubs >= 3)
    conditional_priorities = [
        (Or(clubs > diamonds, And(clubs == 3, diamonds == 3)), opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.LowerMinor


class OneDiamondOpening(Opening):
    call_name = '1D'
    constraints = And(rule_of_twenty, diamonds >= 3)
    conditional_priorities = [
        (diamonds > clubs, opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.HigherMinor


class OneHeartOpening(Opening):
    call_name = '1H'
    constraints = And(rule_of_twenty, hearts >= 5)
    conditional_priorities = [
        (hearts > spades, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.LowerMajor


class OneSpadeOpening(Opening):
    call_name = '1S'
    constraints = And(rule_of_twenty, spades >= 5)
    conditional_priorities = [
        (spades > hearts, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.HigherMajor


response_priorities = enum.Enum(
    "LongestNewMajor",
    "OneSpadeWithFiveResponse",
    "OneHeartWithFiveResponse",
    "OneDiamondResponse",
    "OneHeartWithFourResponse",
    "OneSpadeWithFourResponse",
    "OneNotrumpResponse",
)


class Response(Rule):
    preconditions = [Opened(positions.Partner)]


class OneDiamondResponse(Response):
    call_name = '1D'
    constraints = And(points >= 6, diamonds >= 4)
    priority = response_priorities.OneDiamondResponse


class OneHeartResponse(Response):
    call_name = '1H'
    constraints = And(points >= 6, hearts >= 4)
    conditional_priorities = [
        (And(hearts >= 5, hearts > spades), response_priorities.LongestNewMajor),
        (hearts >= 5, response_priorities.OneHeartWithFiveResponse),
    ]
    priority = response_priorities.OneHeartWithFourResponse


class OneSpadeResponse(Response):
    call_name = '1S'
    constraints = And(points >= 6, spades >= 4)
    conditional_priorities = [
        (spades >= 5, response_priorities.OneSpadeWithFiveResponse)
    ]
    priority = response_priorities.OneSpadeWithFourResponse


class OneNotrumpResponse(Response):
    call_name = '1N'
    constraints = points >= 6
    priority = response_priorities.OneNotrumpResponse


def expr_from_hand(hand):
    return And(
        clubs == len(hand.cards_in_suit(suit.CLUBS)),
        diamonds == len(hand.cards_in_suit(suit.DIAMONDS)),
        hearts == len(hand.cards_in_suit(suit.HEARTS)),
        spades == len(hand.cards_in_suit(suit.SPADES)),
        points == hand.high_card_points()
    )


class PartialOrdering(object):
    def less_than(self, left, right):
        # Our enums are written highest to lowest, so we use > for less_than. :)
        return left > right


class StandardAmericanYellowCard(object):
    rules = [
        OneClubOpening(),
        OneDiamondOpening(),
        OneHeartOpening(),
        OneSpadeOpening(),
        OneDiamondResponse(),
        OneHeartResponse(),
        OneSpadeResponse(),
        OneNotrumpResponse(),
    ]
    priority_ordering = PartialOrdering()


# The dream:
# history.my.knowledge
# history.my.solver
# history.partner.knowledge
# annotations.Opening in history.rho.annotations
# annotations.Opening in history.rho.last_call.annotations


class HistoryView(object):
    def __init__(self, history, position):
        self.history = history
        self.position = position

    @property
    def knowledge(self):
        return self.history.knowledge_for_position(self.position)

    @property
    def annotations(self):
        return self.history.annotations_for_position(self.position)


# This class is immutable.
class History(object):
    def __init__(self):
        self.call_history = CallHistory()
        self._annotation_history = []
        self._constraint_history = []

    @property
    def annotations(self):
        return chain.from_iterable(self._annotation_history)

    def extend_with(self, call, annotations, constraints):
        history = History()
        history.call_history = copy.copy(self.call_history)
        history.call_history.calls.append(call)
        history._annotation_history = self._annotation_history + [annotations]
        history._constraint_history = self._constraint_history + [constraints]
        return history

    def _project_for_position(self, items, position):
        end = -1 - position.index
        start = (len(items) + end) % 4
        return items[start::4]

    def knowledge_for_position(self, position):
        constraints = self._project_for_position(self._constraint_history, position)
        if not constraints:
            return BoolVal(True)
        return And(*constraints)

    def annotations_for_position(self, position):
        return chain.from_iterable(self._project_for_position(self._annotation_history, position))

    @property
    def rho(self):
        return HistoryView(self, positions.RHO)

    @property
    def me(self):
        return HistoryView(self, positions.Me)

    @property
    def partner(self):
        return HistoryView(self, positions.Partner)

    @property
    def lho(self):
        return HistoryView(self, positions.LHO)


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
        self.system = StandardAmericanYellowCard

    def find_call_for(self, hand, call_history):
        history = Interpreter().create_history(call_history)
        # Select highest-intra-bid-priority rules for all possible bids
        rule_selector = RuleSelector(self.system, history)
        # Compute inter-bid priorities for each using the hand.
        possible_calls = rule_selector.possible_calls_for_hand(hand)
        # The resulting priorities are only partially ordered, so have to be walked in a tree.
        maximal_calls = possible_calls.calls_of_maximal_priority()
        # Currently we have no tie-breaking priorities (no planner), so we just select the first call we found.
        if not maximal_calls:
            # If we failed to find any rule able to bid, this is an error.
            return None
        return maximal_calls[0]


class RuleSelector(object):
    def __init__(self, system, history):
        self.system = system
        self.history = history
        self._call_to_rule_cache = None
        self._call_to_compiled_constraints = {}

    def _call_to_rule_map(self):
        if self._call_to_rule_cache is not None:
            return self._call_to_rule_cache

        self._call_to_rule_cache = {}
        for rule in self.system.rules:
            call = rule.create_call(self.history)
            if call:
                exisiting_rule = self._call_to_rule_cache.get(call)
                if not exisiting_rule or rule.category > exisiting_rule.category:
                    self._call_to_rule_cache[call] = rule
        return self._call_to_rule_cache

    # FIXME: This could just use @memoized?
    def rule_for_call(self, call_to_lookup):
        return self._call_to_rule_map().get(call_to_lookup)

    # FIXME: This could just use @memoized?
    def compile_constraints_for_call(self, call_to_lookup):
        constraints = self._call_to_compiled_constraints.get(call_to_lookup)
        if constraints:
            return constraints

        # (Or(clubs > diamonds, clubs == diamonds == 3) AND !(ROT AND hearts >= 5) AND !(ROT AND spades >= 5))
        # OR
        # (!Or(clubs > diamonds, clubs == diamonds == 3) AND !(ROT AND diamonds >=3) AND !(ROT AND hearts >= 5) AND !(ROT AND spades >= 5))

        situations = []
        used_rule = self.rule_for_call(call_to_lookup)
        for priority, condition in used_rule.possible_priorities_and_conditions_for_call(call_to_lookup):
            situational_constraints = [condition]
            for unmade_call, unmade_rule in self._call_to_rule_map().iteritems():
                for unmade_priority, unmade_condition in unmade_rule.possible_priorities_and_conditions_for_call(unmade_call):
                    if unmade_priority < priority: # FIXME: < means > for priority compares.
                        situational_constraints.append(Not(And(unmade_condition, unmade_rule.constraints)))
            situations.append(And(situational_constraints))
        constraints = Or(situations)
        self._call_to_compiled_constraints[call_to_lookup] = constraints
        return constraints

    def possible_calls_for_hand(self, hand):
        possible_calls = PossibleCalls(self.system.priority_ordering)
        for call in CallExplorer().possible_calls_over(self.history.call_history):
            rule = self.rule_for_call(call)
            if not rule:
                continue
            priority = rule.priority_for_call_and_hand(call, hand)
            if priority:
                possible_calls.add_call_with_priority(call, priority)
        return possible_calls


class Interpreter(object):
    def __init__(self):
        # Assuming SAYC for all sides.
        self.system = StandardAmericanYellowCard

    def _select_highest_priority_rule(self, rules):
        # This compares intra-bid priorities and makes sure we are using
        # the right 3H interpretation for this history.
        # This lets us chose conventional bids over natural bids, for instance.
        return rules[0]

    def create_history(self, call_history):
        history = History()
        viewer = call_history.position_to_call()

        for partial_history in call_history.ascending_partial_histories(step=1):
            selector = RuleSelector(self.system, history)

            call = partial_history.last_call()
            rule = selector.rule_for_call(call)
            # We can interpret bids we know how to make.
            constraints = BoolVal(True)
            annotations = []
            if rule:
                annotations.extend(rule.annotations)
                constraints = And(rule.constraints, selector.compile_constraints_for_call(call))
                # FIXME: We should validate the new constraints before saving them in the knowledge.
            history = history.extend_with(call, annotations, constraints)

        return history


solver = Solver()
solver.add(axioms)

interpreter = Interpreter()
history = interpreter.create_history(CallHistory.from_string('1C P 1H'))
solver.add(history.rho.knowledge)
print list(history.rho.annotations)
print solver.check()
print solver.model()

bidder = Bidder()
hand = Hand.from_cdhs_string("A76.65.AKQJ7.432")
print hand
print bidder.find_call_for(hand, CallHistory.from_string("1C P"))
