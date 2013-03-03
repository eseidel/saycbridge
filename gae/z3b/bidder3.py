from z3 import *
from third_party import enum
from core.callhistory import CallHistory
from core.call import Call
from core.hand import Hand
from core.callexplorer import CallExplorer
import core.suit as suit


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

class Rule(object):
    preconditions = []
    category = None
    # FIXME: This is probably not right.
    call_name = None


    def make_call(self, knowlege):
        # FIXME: It's unclear if this should take a call_history or not
        # in the kbb, the call history is not passed to apply_rule.
        for precondition in self.preconditions:
            if not precondition.matches(knowledge):
                return None
        # FIXME: kbb rules can make more than one type of call, it's unclear
        # if we should follow that model here or not.
        return Call(self.call_name)

    def possible_priorities_and_conditions_for_call(self, call):
        # We're eventually going to allow more than one call per rule.
        assert call.name == self.call_name, self.call_name
        for condition, priority in self.conditional_priorities:
            yield priority, condition
        yield self.priority, Bool(True)

    def call_and_priority_for_hand(self, hand):
        solver = Solver()
        solver.add(axioms)
        solver.add(self.constraints)
        solver.add(expr_from_hand(hand))
        if not solver.check():
            return (None, None)

        # FIXME: We may support more calls per rule later.
        call = Call.from_string(self.call_name)
        for condition, priority in self.conditional_priorities:
            solver.push()
            solver.add(condition)
            if solver.check():
                return call, priority
            solver.pop()
        return call, self.priority


opening_priorities = enum.Enum(
    "LongestMajor",
    "HigherMajor",
    "LowerMajor",
    "LongestMinor",
    "HigherMinor",
    "LowerMinor",
)

# FIXME: This is preconditioned on no-one having opened.
class OneClubOpening(Rule):
    call_name = '1C'
    constraints = And(rule_of_twenty, clubs >= 3)
    conditional_priorities = [
        (Or(clubs > diamonds, And(clubs == 3, diamonds == 3)), opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.LowerMinor

class OneDiamondOpening(Rule):
    call_name = '1D'
    constraints = And(rule_of_twenty, diamonds >= 3)
    conditional_priorities = [
        (diamonds > clubs, opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.HigherMinor

class OneHeartOpening(Rule):
    call_name = '1H'
    constraints = And(rule_of_twenty, hearts >= 5)
    conditional_priorities = [
        (hearts > spades, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.LowerMajor

class OneSpadeOpening(Rule):
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

class OneDiamondResponse:
    constraints = And(points >= 6, diamonds >= 4)
    priority = response_priorities.OneDiamondResponse

class OneHeartResponse:
    constraints = And(points >= 6, hearts >= 4)
    conditional_priorities = [
        (And(hearts >= 5, hearts > spades), response_priorities.LongestNewMajor),
        (hearts >= 5, response_priorities.OneHeartWithFiveResponse),
    ]
    priority = response_priorities.OneHeartWithFourResponse

class OneSpadeResponse:
    constraints = And(points >= 6, spades >= 4)
    conditional_priorities = [
        (spades >= 5, response_priorities.OneSpadeWithFiveResponse)
    ]
    priority = response_priorities.OneSpadeWithFourResponse

class OneNotrumpResponse:
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
        return left < right


class StandardAmericanYellowCard(object):
    rules = [
        OneClubOpening(),
        OneDiamondOpening(),
        OneHeartOpening(),
        OneSpadeOpening(),
    ]
    priority_ordering = PartialOrdering()


class Knowledge(object):
    def __init__(self):
        self.me = []
        self.rho = []
        self.partner = []
        self.lho = []

    def rotate(self):
        old_me = self.me
        self.me = self.lho
        self.lho = self.partner
        self.partner = self.rho
        self.rho = old_me


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
        knowledge = Interpreter().knowledge_from_history(call_history)
        # Select highest-intra-bid-priority rules for all possible bids
        rule_selector = RuleSelector(self.system, call_history, knowledge)
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
    def __init__(self, system, call_history, knowledge):
        self._system = system
        self.call_history = call_history
        self.knowledge = knowledge
        self._call_to_rule_cache = None
        self._call_to_compiled_constraints = {}

    def _call_to_rule_map(self):
        if self._call_to_rule_cache is not None:
            return self._call_to_rule_cache

        self._call_to_rule_cache = {}
        for rule in self._system.rules:
            call = rule.make_call(self.knowledge)
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
        possible_calls = PossibleCalls(self._system.priority_ordering)
        for call in CallExplorer().possible_calls_over(self.call_history):
            rule = self.rule_for_call(call)
            if not rule:
                continue
            call, priority = rule.call_and_priority_for_hand(hand)
            if call:
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

    def knowledge_from_history(self, call_history):
        knowledge = Knowledge()
        viewer = call_history.position_to_call()

        for partial_history in call_history.ascending_partial_histories(step=1):
            selector = RuleSelector(self.system, partial_history, knowledge)

            call = partial_history.last_call()
            position_knowledge = knowledge.me
            partial_history_before_last_call = partial_history.copy_with_partial_history(-1)

            rule = selector.rule_for_call(call)
            # We can interpret bids we know how to make.
            if rule:
                new_constraints = [rule.constraints]
                new_constraints.append(selector.compile_constraints_for_call(call))
                # FIXME: We should validate the new constraints before saving them in the knowledge.
                knowledge.me.extend(new_constraints)

            knowledge.rotate()

        return knowledge


# solver = Solver()
# solver.add(axioms)

# print solver.check()

# interpreter = Interpreter()
# solver.add(interpreter.knowledge_from_history(CallHistory.from_string('1C')).rho)
# print solver.check()
# print solver.model()

bidder = Bidder()
hand = Hand.from_cdhs_string("AKQJ7.A76.65.432")
print hand
print bidder.find_call_for(hand, CallHistory.from_string(""))
