# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import datetime
import jinja2
import json
import urllib
import webapp2

jinja_environment = jinja2.Environment(loader=jinja2.FileSystemLoader("templates"))

from core.call import Pass
from core.callexplorer import CallExplorer
from core.callhistory import CallHistory
from proxy import ConstraintsSerializer
from z3b.bidder import Interpreter, Bidder, InconsistentHistoryException
from z3b.forcing import SAYCForcingOracle
from z3b.preconditions import annotations


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
            # sayc_page no longer supported.
        return explore_dict

    # FIXME: Why is this different from ConstraintsSerializer.explore_string?
    # Why does the bidder return one knowledge_string and /explore a different one?
    def _knowledge_string(self, position_view, interpreter):
        explore_string = ConstraintsSerializer(position_view).explore_string()
        # FIXME: Annotation filtering belongs on the client, not here!
        annotations_whitelist = set([annotations.Artificial, annotations.NotrumpSystemsOn])
        annotations_for_last_call = set(position_view.annotations_for_last_call) & annotations_whitelist
        pretty_string = "%s %s" % (explore_string, ", ".join(map(str, annotations_for_last_call)))
        # Only bother trying to interpret if the bid is forcing if we understood it in the first place:
        if position_view.rule_for_last_call:
            try:
                partner_future = interpreter.extend_history(position_view.history, Pass())
                if SAYCForcingOracle().forced_to_bid(partner_future):
                    pretty_string += " Forcing"
            except InconsistentHistoryException:
                pass
        return pretty_string

    # FIXME: This could be untangled further.
    def _knowledge_string_and_rule_for_additional_call(self, history, call, interpreter):
        try:
            history = interpreter.extend_history(history, call)
            knowledge_string = self._knowledge_string(history.rho, interpreter)
            return knowledge_string, history.rho.rule_for_last_call
        except InconsistentHistoryException, e:
            return None, None

    def get(self):
        interpreter = Interpreter()
        calls_string = self.request.get('calls_string') or ''
        dealer_char = self.request.get('dealer') or ''
        vulnerability_string = self.request.get('vulnerability') or ''
        call_history = CallHistory.from_string(calls_string, dealer_char, vulnerability_string)

        interpretations = []
        with interpreter.create_history(call_history) as history:
            for call in CallExplorer().possible_calls_over(call_history):
                knowledge_string, rule = self._knowledge_string_and_rule_for_additional_call(history, call, interpreter)
                explore_dict = self._json_from_rule(knowledge_string, rule, call)
                interpretations.append(explore_dict)

        self.response.headers["Content-Type"] = "application/json"
        self.response.headers["Cache-Control"] = "public"

        expires_date = datetime.datetime.utcnow() + datetime.timedelta(days=1)
        expires_str = expires_date.strftime("%d %b %Y %H:%M:%S GMT")
        self.response.headers.add_header("Expires", expires_str)

        self.response.out.write(json.dumps(interpretations))
