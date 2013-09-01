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


class Explore2Handler(webapp2.RequestHandler):
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

        self.response.out.write(jinja_environment.get_template('explore.html').render({}))
