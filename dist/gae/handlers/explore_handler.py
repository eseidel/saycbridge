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

from proxy import InterpreterProxy

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
        history = self._history_from_calls_string(calls_string)
        # This automatically cleans up our urls for us, which is nice when copy/pasting from unit tests:
        if calls_string and history.comma_separated_calls() != calls_string:
            self._redirect_to_history(history)
            return

        self.response.out.write(jinja_environment.get_template('bid_explorer.html').render({}))


class JSONExploreHandler(webapp2.RequestHandler):
    def _json_from_rule(self, rule, bid):
        if not rule:
            return {}

        return {
            'rule_name': rule.name,
            'priority': rule.priority.index if hasattr(rule, 'priority') and rule.priority else None,
            'explanation': rule.explanation_for_bid(bid),
            'sayc_page': rule.sayc_page_for_bid(bid),
        }

    def get(self):
        interpreter = InterpreterProxy()
        calls_string = self.request.get('calls_string') or ''
        dealer_char = self.request.get('dealer') or ''
        vulnerability_string = self.request.get('vulnerability') or ''
        call_history = CallHistory.from_string(calls_string, dealer_char, vulnerability_string)

        knowledge_string, rule = interpreter.knowledge_string_and_rule_for_last_call(call_history)
        explore_dict = {
            'knowledge_string': knowledge_string,
        }
        explore_dict.update(self._json_from_rule(rule, call_history.calls[-1]))
        self.response.headers["Content-Type"] = "application/json"
        self.response.headers["Cache-Control"] = "public"

        expires_date = datetime.datetime.utcnow() + datetime.timedelta(days=1)
        expires_str = expires_date.strftime("%d %b %Y %H:%M:%S GMT")
        self.response.headers.add_header("Expires", expires_str)

        self.response.out.write(json.dumps(explore_dict))
