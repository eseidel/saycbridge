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
from core.callexplorer import CallExplorer

from kbb.interpreter import BidInterpreter

import json


class ExploreHandler(webapp2.RequestHandler):
    def _history_from_calls_string(self, calls_string):
        history_identifier = "N:NO:%s" % calls_string  # FIXME: I doubt this is right with the new identifiers.
        return CallHistory.from_identifier(history_identifier)

    def _redirect_to_history(self, history):
        self.redirect("/explore/%s" % history.comma_separated_calls())

    def get(self, calls_string=None):
        calls_string = calls_string or ""
        calls_string = urllib.unquote(calls_string)
        calls_string = calls_string.upper()
        history = self._history_from_calls_string(calls_string)
        # This automatically cleans up our urls for us, which is nice when copy/pasting from unit tests:
        if calls_string and history.comma_separated_calls() != calls_string:
            self._redirect_to_history(history)
            return

        interpreter = BidInterpreter()
        possible_calls = []
        history_for_next_to_bid = history.copy_with_history_until_after_last_call_from_position(history.position_to_call())
        existing_knowledge, knowledge_builder = interpreter.knowledge_from_history(history)

        for future in CallExplorer().possible_futures(history):
            knowledge, consuming_rule = interpreter.knowledge_including_new_bid(knowledge_builder, future.last_call(), loose_constraints=True)
            possible_calls.append([future.last_call(), consuming_rule, knowledge])

        template_values = {
            'call_history': history,
            'possible_calls': possible_calls,
            'knowledge_positions': existing_knowledge.absolute_positions(history.position_to_call()),
        }
        self.response.out.write(jinja_environment.get_template('bid_explorer.html').render(template_values))


class JSONExploreHandler(webapp2.RequestHandler):
    def _json_from_rule(self, rule, bid):
        if not rule:
            return {}

        return {
            'rule_name': rule.name(),
            'priority': rule.priority.index if rule.priority else None,
            'explanation': rule.explanation_for_bid(bid),
            'sayc_page': rule.sayc_page_for_bid(bid),
        }

    def get(self):
        interpreter = BidInterpreter()
        calls_string = self.request.get('calls_string') or ''
        dealer_char = self.request.get('dealer') or ''
        vulnerability_string = self.request.get('vulnerability') or ''
        history = CallHistory.from_string(calls_string, dealer_char, vulnerability_string)

        existing_knowledge, knowledge_builder = interpreter.knowledge_from_history(history)
        matched_rules = knowledge_builder.matched_rules()
        explore_dict = {
            'knowledge_string': existing_knowledge.rho.pretty_one_line(include_last_call_name=False) if existing_knowledge else None,
        }
        explore_dict.update(self._json_from_rule(matched_rules[-1], history.calls[-1]))
        self.response.headers["Content-Type"] = "application/json"
        self.response.headers["Cache-Control"] = "public"

        expires_date = datetime.datetime.utcnow() + datetime.timedelta(days=1)
        expires_str = expires_date.strftime("%d %b %Y %H:%M:%S GMT")
        self.response.headers.add_header("Expires", expires_str)

        self.response.out.write(json.dumps(explore_dict))
