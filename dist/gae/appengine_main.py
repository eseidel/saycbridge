#!/usr/bin/env python
# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import webapp2

from handlers.autobid_handler import JSONAutobidHandler
from handlers.explore_handler import ExploreHandler, JSONExploreHandler
from handlers.explore2_handler import Explore2Handler, JSONExplore2Handler
from handlers.new_bidder_handler import NewBidderHandler
from handlers.scores_handler import ScoresHandler
from handlers.score_flashcards_handler import ScoreFlashcardsHandler
from handlers.unittest_handler import UnittestHandler
from handlers.priorities_handler import JSONPrioritiesHandler


routes = [
    ('/', NewBidderHandler),
    (r'/explore/(.*)', ExploreHandler),
    (r'/explore', ExploreHandler),
    (r'/explore2/(.*)', Explore2Handler),
    (r'/explore2', Explore2Handler),
    (r'/unittests', UnittestHandler),
    (r'/json/autobid', JSONAutobidHandler),
    (r'/json/interpret', JSONExploreHandler),
    (r'/json/interpret2', JSONExplore2Handler),
    (r'/bid', NewBidderHandler),
    (r'/bid/.*', NewBidderHandler),
    (r'/play', NewBidderHandler),
    (r'/play/.*', NewBidderHandler),
    (r'/scores', ScoresHandler),
    (r'/scoring', ScoreFlashcardsHandler),
    (r'/scoring/.*', ScoreFlashcardsHandler),
    (r'/json/priorities', JSONPrioritiesHandler),

    # Deprecated handlers:
    (r'/bidder', NewBidderHandler),
    (r'/bidder/.*', NewBidderHandler),
    (r'/autobid/.*', NewBidderHandler),  # exists for compatibility with old URLs.
    (r'/new_bidder', NewBidderHandler),
    (r'/new_bidder/.*', NewBidderHandler),
]

app = webapp2.WSGIApplication(routes, debug=True)
