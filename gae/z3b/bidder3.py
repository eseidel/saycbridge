from z3 import *
from third_party import enum

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
# Tie-breaker-priorites -- planner stage, when 2 bids match which we make.

class Rule(object):
    pass


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
    constraints = [rule_of_twenty, clubs >= 3]
    conditional_priorites = [
        (Or(clubs > diamonds, clubs == diamonds == 3), opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.LowerMinor

class OneDiamondOpening(Rule):
    constraints = [rule_of_twenty, diamonds >= 3]
    conditional_priorites = [
        (diamonds > clubs, opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.HigherMinor

class OneHeartOpening(Rule):
    constraints = [rule_of_twenty, hearts >= 5]
    conditional_priorites = [
        (hearts > spades, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.LowerMajor

class OneSpadeOpening(Rule):
    constraints = [rule_of_twenty, spades >= 5]
    conditional_priorites = [
        (spades > hearts, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.HigherMajor


response_priorites = enum.Enum(
    "LongestNewMajor",
    "OneSpadeWithFiveResponse",
    "OneHeartWithFiveResponse",
    "OneDiamondResponse",
    "OneHeartWithFourResponse",
    "OneSpadeWithFourResponse",
    "OneNotrumpResponse",
)

class OneDiamondResponse:
    constraints = [points >= 6, diamonds >= 4]
    priority = response_priorites.OneDiamondResponse

class OneHeartResponse:
    constraints = [points >= 6, hearts >= 4]
    conditional_priorites = [
        (And(hearts >= 5, hearts > spades), response_priorites.LongestNewMajor),
        (hearts >= 5, response_priorites.OneHeartWithFiveResponse),
    ]
    priority = response_priorites.OneHeartWithFourResponse

class OneSpadeResponse:
    constraints = [points >= 6, spades >= 4]
    conditional_priorites = [
        (spades >= 5, response_priorites.OneSpadeWithFiveResponse)
    ]
    priority = response_priorites.OneSpadeWithFourResponse

class OneNotrumpResponse:
    constraints = [points >= 6]
    priority = response_priorites.OneNotrumpResponse


class PositionKnowledge(object):
    def __init__(self):
        self._exprs = []

    def add(exprs):
        self._exprs.extend(exprs)


class Knowledge(object):
    def __init__(self):
        self.me = PositionKnowledge()
        self.rho = PositionKnowledge()
        self.partner = PositionKnowledge()
        self.lho = PositionKnowledge()

    def rotate(self):
        old_me = self.me
        self.me = self.lho
        self.lho = self.partner
        self.partner = self.rho
        self.rho = old_me

class Bidder(object):
    pass


class Interpreter(object):
    rules = [
        OneClubOpening(),
        OneDiamondOpening(),
        OneHeartOpening(),
        OneSpadeOpening(),
    ]

    def _constraints_for_calls_with_priorites_greater_than(self, priority, call_history, knowledge):
        # Generate a mapping of bid -> fitting rules
        # Sort fitting rules for each bid, based on priority
        # generate a map of bid -> highest_priority rule
        # walk this list of rules, and grab each set of possible priorities, priority_conditions
        # if !(possible_priority <= priority), then add it to the list of 
        # return a list of priority_conditions + constraints
        # FIXME: Isn't SuitedToPlay always going to contribute many available bids?
        # We should probably only consult rules if they can produce bids of higher priority.
        rules = [rule for rule in self.rules if rule.matches_preconditions(call_history, knowledge)]
        bid_to_priority_and_constraints
        for rule in rules:
            rule.add_constraints_for_all_conditions_above_priority(priority, )


    def _select_highest_priority_rule(self, rules):
        # This compares intra-bid priorities and makes sure we are using
        # the right 3H interpretation for this history.
        # This lets us chose conventional bids over natural bids, for instance.
        return rules[0]

    def knowledge_from_history(self, call_history):
        knowledge = Knowledge()
        viewer = call_history.position_to_call()

        for partial_history in call_history.ascending_partial_histories(step=1):
            call = partial_history.last_call()
            caller = partial_history.last_to_call()
            position_knowledge = knowlege.me
            partial_history_before_last_call = partial_history.copy_with_partial_history(-1)

            # First get all the rules who have something to say about this call history.
            # This checks pre-conditions, as well as for the presence of this particular call.
            rules = [rule for rule in self.rules if rule.could_generate_last_call(call_history, knowledge)]
            # Select the one with the highest intra-bid priority.  There should be exactly one.
            rule = self._select_highest_priority_rule(rules)

            # Now we know which rule they must have used to make this bid, we need to know which priorities it could have been.
            # FIXME: We could simplify the list of priorities down to the lowest non-comparible priorities.
            for priority in rule.possible_priorities_for_call(partial_history):
                for constraints in self._constraints_for_calls_with_priorites_greater_than(priority, partial_history_before_last_call, knowledge):
                    # They didn't make this bid, so !(condition AND constraints) --> add to knowledge
                    position_knowledge.add(Not(constraints))
            knowledge.rotate()

        return knowledge
            # Take the set of bids which have higher inter-bid priority than the bids your partner made
            # For each possible prio bid, for each possible priority of that bid
            # if that possible priority is higher than the pri
            # take the negation of their constrait.  Add that knowledge to their hand.
            # take the bid they did make, and add that knowledge to their hand.


            # (Or(clubs > diamonds, clubs == diamonds == 3) AND !(ROT AND hearts >= 5) AND !(ROT AND spades >= 5))
            # OR
            # (!Or(clubs > diamonds, clubs == diamonds == 3) AND !(ROT AND diamonds >=3) AND !(ROT AND hearts >= 5) AND !(ROT AND spades >= 5))


solver = Solver()
solver.add(axioms)

print solver.check()
