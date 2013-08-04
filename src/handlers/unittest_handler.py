# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from __future__ import with_statement

import urllib
import re

import webapp2
import jinja2
import os

jinja_environment = jinja2.Environment(loader=jinja2.FileSystemLoader("templates"))


class UnittestHandler(webapp2.RequestHandler):
    unittest_file_path = "core/sayc_unittest.py"
    baseline_file_path = "z3b_baseline.txt"

    test_method_regexp = re.compile(r"\s+def (test_\w*)\(")

    def _compute_test_method_lines(self, unittest_file_path):
        method_name_to_line = {}
        with open(unittest_file_path) as unittest_file:
            # FIXME: In python 2.6 and later we could pass start=1 to enumerate.
            for line_number, line in enumerate(unittest_file.readlines()):
                match_object = self.test_method_regexp.match(line)
                if match_object:
                    method_name_to_line[match_object.group(1)] = line_number + 1
        return method_name_to_line

    def _link_to_file(self, file_path, line_number=None):
        base_url = "https://github.com/eseidel/saycbot/blob/master"
        url_to_file = "%s/%s" % (base_url, file_path)
        if line_number:
            url_to_file += "#L%s" % line_number
        return url_to_file

    def _test_name_header(self, test_name, line_number=None):
        if not line_number:
            return test_name
        return "<a href='%s'>%s</a>" % (self._link_to_file(self.unittest_file_path, line_number), test_name)

    hand_regexp = re.compile("(\w*\.\w*\.\w*\.\w*)")

    # Split out history matching to avoid matching Call('2D') as a history.
    history_matcher = "((?:(?:\d(?:C|D|H|S|N)|P|X|XX)\s?)+)"
    history_regexp = re.compile("history: %s" % history_matcher)
    subtest_of_regexp = re.compile("subtest of %s" % history_matcher)
    test_name_header_regexp = re.compile(r"(test_\w+)")

    def _page_from_unittest_output(self, output_file_path):
        test_method_lines = self._compute_test_method_lines(self.unittest_file_path)
        test_link = lambda test_name: self._test_name_header(test_name, test_method_lines.get(test_name))
        test_link_from_match = lambda match: test_link(match.group(0))

        with open(output_file_path) as output_file:
            file_contents = output_file.read()
            file_contents = file_contents.replace("\n", "<br>")
            file_contents = file_contents.replace("FAIL", "<font color='red'>FAIL</font>")
            file_contents = file_contents.replace("WARNING", "<font color='orange'>WARNING</font>")
            file_contents = self.hand_regexp.sub(r"<a href='/hand/\1'>\1</a>", file_contents)
            file_contents = self.history_regexp.sub(r"history: <a href='/explore/\1'>\1</a>", file_contents)
            file_contents = self.subtest_of_regexp.sub(r"subtest of <a href='/explore/\1'>\1</a>", file_contents)
            file_contents = self.test_name_header_regexp.sub(test_link_from_match, file_contents)
            return file_contents

    def get(self):
        template_values = {
            "unittests_output": self._page_from_unittest_output(self.baseline_file_path),
            "unittest_file_name": self.baseline_file_path,
        }
        self.response.out.write(jinja_environment.get_template('unittests.html').render(template_values))
