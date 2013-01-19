#!/usr/bin/env python

import webapp2

from handlers.bidder_handler import JSONAutobidHandler
from handlers.explore_handler import ExploreHandler, JSONExploreHandler
from handlers.new_bidder_handler import NewBidderHandler
from handlers.scores_handler import ScoresHandler
from handlers.score_flashcards_handler import ScoreFlashcardsHandler
from handlers.unittest_handler import UnittestHandler


routes = [
    ('/', NewBidderHandler),
    (r'/explore/(.*)', ExploreHandler),
    (r'/explore', ExploreHandler),
    (r'/unittests', UnittestHandler),
    (r'/json/autobid', JSONAutobidHandler),
    (r'/json/interpret', JSONExploreHandler),
    (r'/bid', NewBidderHandler),
    (r'/bid/.*', NewBidderHandler),
    (r'/play', NewBidderHandler),
    (r'/play/.*', NewBidderHandler),
    (r'/scores', ScoresHandler),
    (r'/scoring', ScoreFlashcardsHandler),
    (r'/scoring/.*', ScoreFlashcardsHandler),

    # Deprecated handlers:
    (r'/bidder', NewBidderHandler),
    (r'/bidder/.*', NewBidderHandler),
    (r'/autobid/.*', NewBidderHandler),  # exists for compatibility with old URLs.
    (r'/new_bidder', NewBidderHandler),
    (r'/new_bidder/.*', NewBidderHandler),
]


app = webapp2.WSGIApplication(routes, debug=True)
