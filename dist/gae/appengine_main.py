#!/usr/bin/env python
# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import webapp2

from handlers.autobid_handler import JSONAutobidHandler
from handlers.explore_handler import ExploreHandler, JSONExploreHandler
from handlers.bidder_handler import BidderHandler
from handlers.scores_handler import ScoresHandler
from handlers.score_flashcards_handler import ScoreFlashcardsHandler
from handlers.unittest_handler import UnittestHandler
from handlers.priorities_handler import JSONPrioritiesHandler


routes = [
    ('/', BidderHandler),
    (r'/bid', BidderHandler),
    (r'/bid/.*', BidderHandler),
    (r'/explore/(.*)', ExploreHandler),
    (r'/explore', ExploreHandler),
    (r'/json/autobid', JSONAutobidHandler),
    (r'/json/interpret', JSONExploreHandler),

    # Low usage:
    (r'/scores', ScoresHandler),
    (r'/scoring', ScoreFlashcardsHandler),
    (r'/scoring/.*', ScoreFlashcardsHandler),

    # Don't actually work:
    (r'/play', BidderHandler),
    (r'/play/.*', BidderHandler),
    (r'/json/priorities', JSONPrioritiesHandler),

    # Debugging:
    (r'/unittests', UnittestHandler),

    # Back-compat:
    (r'/explore2/(.*)', ExploreHandler),
    (r'/explore2', ExploreHandler),
    (r'/json/interpret2', JSONExploreHandler),
]

app = webapp2.WSGIApplication(routes, debug=True)
