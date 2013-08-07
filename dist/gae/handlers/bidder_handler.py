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
from core.position import position_from_char
from core.autobidder import Autobidder

from proxy import BidderProxy

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
        # Note: We keep bids_string around to I can test old requests.
        calls_string = self.request.get('calls_string') or self.request.get('bids_string') or ''
        history = CallHistory.from_string(calls_string, dealer_char, vulnerability_string)
        return Board(board_number, deal, history)

    def _json_tuple(self, bid, rule, hand_knowledge):
        json_tuple = [None, None, None, None, None]
        if bid:
            json_tuple[0] = bid.name
        if rule:
            json_tuple[1] = rule.name
        if hand_knowledge:
            json_tuple[2] = hand_knowledge.pretty_one_line(include_last_call_name=False)
        if rule and bid:
            json_tuple[3] = rule.explanation_for_bid(bid)
            json_tuple[4] = rule.sayc_page_for_bid(bid)
        return json_tuple

    def _json_for_interpretations(self, bids_and_rules_and_hand_knowledges):
        return [self._json_tuple(bid, rule, hand_knowledge) for bid, rule, hand_knowledge in bids_and_rules_and_hand_knowledges]

    def get(self):
        bidder = BidderProxy()
        autobidder = Autobidder(bidder)
        board = self._board_from_request()
        until_position_string = self.request.get('until_position')
        until_position = position_from_char(until_position_string) if until_position_string else None
        bids_and_rules_and_hand_knowledges = autobidder.bid_all_hands(board, until_position=until_position)
        current_history = copy.deepcopy(board.call_history)
        bids_and_rules_and_hand_knowledges += autobidder.bid_all_hands(board)
        # Callers might want to know what the full history would look like if autobid.
        board_dict = {
            'board_number': board.number,
            'calls_string': current_history.calls_string(),
            'autobid_continuation': board.call_history.calls_string(),
            'autobid_interpretations': self._json_for_interpretations(bids_and_rules_and_hand_knowledges),
        }
        self.response.headers["Content-Type"] = "application/json"
        self.response.headers["Cache-Control"] = "public"

        expires_date = datetime.datetime.utcnow() + datetime.timedelta(days=1)
        expires_str = expires_date.strftime("%d %b %Y %H:%M:%S GMT")
        self.response.headers.add_header("Expires", expires_str)

        self.response.out.write(json.dumps(board_dict))
