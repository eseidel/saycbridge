#!/usr/bin/env python
# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import webapp2

from handlers.autobid_handler import JSONAutobidHandler
from handlers.explore2_handler import Explore2Handler, JSONExplore2Handler
from handlers.bidder_handler import BidderHandler
from handlers.scores_handler import ScoresHandler
from handlers.score_flashcards_handler import ScoreFlashcardsHandler
from handlers.unittest_handler import UnittestHandler
from handlers.priorities_handler import JSONPrioritiesHandler


routes = [
    ('/', BidderHandler),
    (r'/explore/(.*)', Explore2Handler),
    (r'/explore', Explore2Handler),
    (r'/explore2/(.*)', Explore2Handler),
    (r'/explore2', Explore2Handler),
    (r'/unittests', UnittestHandler),
    (r'/json/autobid', JSONAutobidHandler),
    (r'/json/interpret', JSONExplore2Handler),
    (r'/json/interpret2', JSONExplore2Handler),
    (r'/bid', BidderHandler),
    (r'/bid/.*', BidderHandler),
    (r'/play', BidderHandler),
    (r'/play/.*', BidderHandler),
    (r'/scores', ScoresHandler),
    (r'/scoring', ScoreFlashcardsHandler),
    (r'/scoring/.*', ScoreFlashcardsHandler),
    (r'/json/priorities', JSONPrioritiesHandler),
]

app = webapp2.WSGIApplication(routes, debug=True)
