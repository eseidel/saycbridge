#!/usr/bin/env python3
"""CLI wrapper for the z3b bidder engine.

Provides the same JSON output as the old z3b web API, but as a
command-line tool called directly by yarborough's bidder_fight and
explorer_fight.

Subcommands:
    autobid    – bid all four hands, print JSON to stdout
    interpret  – interpret possible calls at a position, print JSON to stdout

Usage:
    # From the saycbridge repo root:
    PYTHONPATH=src .venv/bin/python z3b_cli.py autobid \
        --dealer N --vulnerability None \
        --north "AKJ5.A84.J7.KJ63" --east "T987.K73.AK83.74" \
        --south "Q62.QJT.T965.AT5" --west "43.9652.Q42.Q982"

    PYTHONPATH=src .venv/bin/python z3b_cli.py interpret \
        --calls "1S,P" --dealer N --vulnerability None
"""

import argparse
import json
import sys
import os

# Add src/ to the Python path so z3b/core imports work.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "src"))

from core.board import Board
from core.call import Pass
from core.callexplorer import CallExplorer
from core.callhistory import CallHistory
from core.deal import Deal
from core.position import Position
from core.suit import SUITS
from z3b.bidder import Bidder, Interpreter, InconsistentHistoryException
from z3b.forcing import SAYCForcingOracle
from z3b.preconditions import annotations


# ---------------------------------------------------------------------------
# Helpers ported from the old GAE handlers
# ---------------------------------------------------------------------------

class ConstraintsSerializer:
    MAX_HCP_PER_HAND = 37
    EMPTY_HCP_RANGE = (0, MAX_HCP_PER_HAND)

    def __init__(self, position_view):
        self._hcp_range = (position_view.min_points, position_view.max_points)
        self._suit_length_ranges = [
            (position_view.min_length(suit), position_view.max_length(suit))
            for suit in SUITS
        ]

    def _string_for_range(self, range_tuple, global_max):
        min_value, max_value = range_tuple
        if min_value == max_value:
            return str(min_value)
        if min_value == 0 and max_value >= global_max:
            return "?"
        if max_value >= global_max:
            return "%s+" % min_value
        return "%s-%s" % (min_value, max_value)

    def _pretty_string_for_suit(self, suit):
        suit_string = self._string_for_range(self._suit_length_ranges[suit.index], 6)
        if suit_string == "?":
            return None
        return suit_string + suit.char

    def explore_string(self):
        if (self._hcp_range == self.EMPTY_HCP_RANGE
                and self._suit_length_ranges.count((0, 13)) == 4):
            return "?"
        suit_strings = [self._pretty_string_for_suit(suit) for suit in SUITS]
        suit_strings = [s for s in suit_strings if s]
        pretty_string = "%s hcp" % self._string_for_range(
            self._hcp_range, self.MAX_HCP_PER_HAND)
        if suit_strings:
            return "%s, %s" % (pretty_string, " ".join(suit_strings))
        return pretty_string


def _explore_string_from_call_selection(interpreter, selection):
    try:
        with interpreter.extend_history(
                selection.rule_selector.history, selection.call) as history:
            return ConstraintsSerializer(history.rho).explore_string()
    except InconsistentHistoryException:
        return None


def _json_tuple(interpreter, selection):
    json_tuple = [None, None, None, None, None]
    if not selection:
        return json_tuple
    if selection.call:
        json_tuple[0] = selection.call.name
    if selection.rule:
        json_tuple[1] = selection.rule.name
    if selection.call:
        json_tuple[2] = _explore_string_from_call_selection(interpreter, selection)
    if selection.rule and selection.call:
        json_tuple[3] = selection.rule.explanation_for_bid(selection.call)
        json_tuple[4] = None
    return json_tuple


def _knowledge_string(position_view, interpreter):
    explore_string = ConstraintsSerializer(position_view).explore_string()
    annotations_whitelist = {annotations.Artificial, annotations.NotrumpSystemsOn}
    annotations_for_last_call = (
        set(position_view.annotations_for_last_call) & annotations_whitelist
    )
    pretty_string = "%s %s" % (
        explore_string, ", ".join(map(str, annotations_for_last_call))
    )
    if position_view.rule_for_last_call:
        try:
            partner_future = interpreter.extend_history(
                position_view.history, Pass()
            )
            if SAYCForcingOracle().forced_to_bid(partner_future):
                pretty_string += " Forcing"
        except InconsistentHistoryException:
            pass
    return pretty_string


def _knowledge_string_and_rule(history, call, interpreter):
    try:
        history = interpreter.extend_history(history, call)
        ks = _knowledge_string(history.rho, interpreter)
        return ks, history.rho.rule_for_last_call
    except InconsistentHistoryException:
        return None, None


# ---------------------------------------------------------------------------
# autobid
# ---------------------------------------------------------------------------

def do_autobid(args):
    deal = Deal.from_string(
        "%s %s %s %s" % (args.north, args.east, args.south, args.west)
    )
    history = CallHistory.from_string(
        args.calls or "", args.dealer, args.vulnerability
    )
    board = Board(args.number, deal, history)

    bidder = Bidder()
    interpreter = Interpreter()

    until_position = (
        Position.from_char(args.until_position) if args.until_position else None
    )

    call_selections = []
    while (not board.call_history.is_complete()
           and board.call_history.position_to_call() != until_position):
        pos = board.call_history.position_to_call()
        hand = board.deal.hands[pos.index]
        selection = bidder.call_selection_for(hand, board.call_history)
        call = selection.call if selection and selection.call else Pass()
        board.call_history.calls.append(call)
        call_selections.append(selection)

    until_position_history_string = board.call_history.calls_string()

    while not board.call_history.is_complete():
        pos = board.call_history.position_to_call()
        hand = board.deal.hands[pos.index]
        selection = bidder.call_selection_for(hand, board.call_history)
        call = selection.call if selection and selection.call else Pass()
        board.call_history.calls.append(call)
        call_selections.append(selection)

    result = {
        "board_number": board.number,
        "calls_string": until_position_history_string,
        "autobid_continuation": board.call_history.calls_string(),
        "autobid_interpretations": [
            _json_tuple(interpreter, s) for s in call_selections
        ],
    }
    json.dump(result, sys.stdout)
    sys.stdout.write("\n")


# ---------------------------------------------------------------------------
# interpret
# ---------------------------------------------------------------------------

def do_interpret(args):
    call_history = CallHistory.from_string(
        args.calls or "", args.dealer, args.vulnerability
    )

    interpreter = Interpreter()
    interpretations = []
    with interpreter.create_history(call_history) as history:
        for call in CallExplorer().possible_calls_over(call_history):
            ks, rule = _knowledge_string_and_rule(history, call, interpreter)
            explore_dict = {"call_name": call.name}
            if ks is not None:
                explore_dict["knowledge_string"] = ks
            if rule:
                explore_dict["rule_name"] = rule.name
                if hasattr(rule, "priority") and rule.priority:
                    explore_dict["priority"] = rule.priority.index
                explanation = rule.explanation_for_bid(call)
                if explanation is not None:
                    explore_dict["explanation"] = explanation
            interpretations.append(explore_dict)

    json.dump(interpretations, sys.stdout)
    sys.stdout.write("\n")


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="z3b bidder CLI")
    subparsers = parser.add_subparsers(dest="command", required=True)

    # -- autobid -----------------------------------------------------------
    ab = subparsers.add_parser("autobid", help="Bid all four hands")
    ab.add_argument("--number", type=int, default=1, help="Board number")
    ab.add_argument("--dealer", default="N", help="Dealer position (N/E/S/W)")
    ab.add_argument("--vulnerability", default="None",
                    help="Vulnerability (None/N-S/E-W/Both)")
    ab.add_argument("--north", required=True, help="North hand (C.D.H.S)")
    ab.add_argument("--east", required=True, help="East hand (C.D.H.S)")
    ab.add_argument("--south", required=True, help="South hand (C.D.H.S)")
    ab.add_argument("--west", required=True, help="West hand (C.D.H.S)")
    ab.add_argument("--calls", default="", help="Existing call history")
    ab.add_argument("--until-position", default="",
                    help="Stop bidding at this position")

    # -- interpret ---------------------------------------------------------
    ip = subparsers.add_parser("interpret",
                               help="Interpret possible calls at a position")
    ip.add_argument("--calls", default="", help="Call history (comma or space separated)")
    ip.add_argument("--dealer", default="N", help="Dealer position (N/E/S/W)")
    ip.add_argument("--vulnerability", default="None",
                    help="Vulnerability (None/N-S/E-W/Both)")

    args = parser.parse_args()

    if args.command == "autobid":
        do_autobid(args)
    elif args.command == "interpret":
        do_interpret(args)


if __name__ == "__main__":
    main()
