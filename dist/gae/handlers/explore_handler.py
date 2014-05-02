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

def get_git_revision():
    import subprocess
    proc = subprocess.Popen(['git', 'rev-parse', 'HEAD'], stdout=subprocess.PIPE)
    return proc.stdout.readline().rstrip()
BIDDER_REVISION = get_git_revision()


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

        self.response.out.write(jinja_environment.get_template('explore.html').render(
            dict(bidder_revision=BIDDER_REVISION)))


class JSONExploreHandler(webapp2.RequestHandler):
    def _set_if_not_none(self, dictionary, key, value):
        if value is not None:
            dictionary[key] = value

    def _json_from_rule(self, knowledge_string, rule, call):
        explore_dict = { 'call_name': call.name }
        self._set_if_not_none(explore_dict, 'knowledge_string', knowledge_string)
        if rule:
            explore_dict['rule_name'] = rule.name
            priority = rule.priority.index if hasattr(rule, 'priority') and rule.priority else None
            self._set_if_not_none(explore_dict, 'priority', priority)
            self._set_if_not_none(explore_dict, 'explanation', rule.explanation_for_bid(call))
            self._set_if_not_none(explore_dict, 'sayc_page', rule.sayc_page_for_bid(call))
        return explore_dict

    def get(self):
        interpreter = InterpreterProxy()
        calls_string = self.request.get('calls_string') or ''
        dealer_char = self.request.get('dealer') or ''
        vulnerability_string = self.request.get('vulnerability') or ''
        call_history = CallHistory.from_string(calls_string, dealer_char, vulnerability_string)

        interpretations = []
        with interpreter.create_history(call_history) as history:
            for call in CallExplorer().possible_calls_over(call_history):
                knowledge_string, rule = interpreter.knowledge_string_and_rule_for_additional_call(history, call)
                explore_dict = self._json_from_rule(knowledge_string, rule, call)
                interpretations.append(explore_dict)

        self.response.headers["Content-Type"] = "application/json"
        self.response.headers["Cache-Control"] = "public"

        expires_date = datetime.datetime.utcnow() + datetime.timedelta(days=1)
        expires_str = expires_date.strftime("%d %b %Y %H:%M:%S GMT")
        self.response.headers.add_header("Expires", expires_str)

        self.response.out.write(json.dumps(interpretations))
