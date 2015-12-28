# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import copy
import datetime
import urllib

import webapp2
import jinja2
import os

jinja_environment = jinja2.Environment(loader=jinja2.FileSystemLoader("templates"))

from core.callhistory import CallHistory
from core.board import Board
from core.deal import Deal
from core.position import Position
from core.call import Pass
from z3b.bidder import Interpreter, Bidder, InconsistentHistoryException

from proxy import ConstraintsSerializer

import json


class JSONAutobidHandler(webapp2.RequestHandler):
    def _board_from_request(self):
        board_number = int(self.request.get('number'))
        vulnerability_string = self.request.get('vunerability')
        hand_strings = map(str, [
            self.request.get('deal[north]'),
            self.request.get('deal[east]'),
            self.request.get('deal[south]'),
            self.request.get('deal[west]'),
        ])

        deal = Deal.from_string(' '.join(hand_strings))
        dealer_char = self.request.get('dealer')
        calls_string = self.request.get('calls_string', '')
        history = CallHistory.from_string(calls_string, dealer_char, vulnerability_string)
        return Board(board_number, deal, history)

    # FIXME: This is a hack.
    def _explore_string_from_call_selection(self, selection):
        try:
            with Interpreter().extend_history(selection.rule_selector.history, selection.call) as history:
                return ConstraintsSerializer(history.rho).explore_string()
        except InconsistentHistoryException:
            return None

    def _json_tuple(self, selection):
        json_tuple = [None, None, None, None, None]
        if not selection:
            return json_tuple
        if selection.call:
            json_tuple[0] = selection.call.name
        if selection.rule:
            json_tuple[1] = selection.rule.name
        if selection.call:
            json_tuple[2] = self._explore_string_from_call_selection(selection)
        if selection.rule and selection.call:
            json_tuple[3] = selection.rule.explanation_for_bid(selection.call)
            json_tuple[4] = None # Was sayc_page_for_bid.
        return json_tuple

    def _bid_all_hands(self, bidder, board, until_position=None):
        call_selections = []
        while not board.call_history.is_complete() and board.call_history.position_to_call() != until_position:
            position_to_call = board.call_history.position_to_call()
            hand = board.deal.hands[position_to_call.index]
            selection = bidder.call_selection_for(hand, board.call_history)
            call = selection.call if selection and selection.call else Pass()
            board.call_history.calls.append(call)
            call_selections.append(selection)
        return call_selections

    def get(self):
        bidder = Bidder()
        board = self._board_from_request()
        until_position_string = self.request.get('until_position')
        until_position = Position.from_char(until_position_string) if until_position_string else None
        call_selections = self._bid_all_hands(bidder, board, until_position=until_position)
        until_position_history_string = board.call_history.calls_string()
        call_selections += self._bid_all_hands(bidder, board)
        # Callers might want to know what the full history would look like if autobid.
        board_dict = {
            'board_number': board.number,
            'calls_string': until_position_history_string, # The history up to "until_position"
            'autobid_continuation': board.call_history.calls_string(), # How the autobidder would continue
            'autobid_interpretations': map(self._json_tuple, call_selections), # Interpretations for all calls (including continuation)
        }
        self.response.headers["Content-Type"] = "application/json"
        self.response.headers["Cache-Control"] = "public"

        expires_date = datetime.datetime.utcnow() + datetime.timedelta(days=1)
        expires_str = expires_date.strftime("%d %b %Y %H:%M:%S GMT")
        self.response.headers.add_header("Expires", expires_str)

        self.response.out.write(json.dumps(board_dict))
