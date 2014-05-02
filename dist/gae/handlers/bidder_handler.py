# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import webapp2
import jinja2
import os

jinja_environment = jinja2.Environment(loader=jinja2.FileSystemLoader("templates"))


class BidderHandler(webapp2.RequestHandler):
    def get(self):
        self.response.out.write(jinja_environment.get_template('bidder.html').render())
