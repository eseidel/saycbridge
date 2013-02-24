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

# Intra-bid priorities, first phase, "interpretation priorities"
# Inter-bid priorities, "which do you look at first"
# Tie-breaker-priorites -- planner stage.

opening_priorities = enum.Enum(
    "LongestMajor",
    "HigherMajor",
    "LowerMajor",
    "LongestMinor",
    "HigherMinor",
    "LowerMinor",
)

# FIXME: This is preconditioned on no-one having opened.
class OneClubOpening:
    constraints = [rule_of_twenty, clubs >= 3]
    conditional_priorites = [
        (Or(clubs > diamonds, clubs == diamonds == 3), opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.LowerMinor

class OneDiamondOpening:
    constraints = [rule_of_twenty, diamonds >= 3]
    conditional_priorites = [
        (diamonds > clubs, opening_priorities.LongestMinor),
    ]
    priority = opening_priorities.HigherMinor

class OneHeartOpening:
    constraints = [rule_of_twenty, hearts >= 5]
    conditional_priorites = [
        (hearts > spades, opening_priorities.LongestMajor),
    ]
    priority = opening_priorities.LowerMajor

class OneSpadeOpening:
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


solver = Solver()
solver.add(axioms)

print solver.check()
