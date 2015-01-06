#!/usr/bin/env python
# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import logging
import sys
import find_src

from factory import BidderFactory
from core.call import Call, Pass
from core.board import Board
from core.suit import *
from core.position import Position


class SAYCBot(object):
    def __init__(self):
        self.verbose = False

    def _print_bidding_result(self, call_history):
        print "Bids:", call_history.calls_string()
        if call_history.is_passout():
            print "Pass Out"
        else:
            contract = call_history.contract()
            declarer = call_history.declarer()
            print "%s by %s" % (contract, declarer.name)

    def _print_hands(self, deal):
        for position, hand in enumerate(deal.hands):
            print "%s: %s" % (Position.from_index(position).name, hand.pretty_one_line())

    def _bid_board(self, board, bidder):
        print "Board:", board.identifier
        while not board.call_history.is_complete():
            position_to_call = board.call_history.position_to_call().index
            hand = board.deal.hands[position_to_call]
            bid = bidder.find_call_for(hand, board.call_history)
            if not bid:
                print "NO BID in board: %s" % board.identifier
                bid = Pass()
            board.call_history.calls.append(bid)
        if self.verbose:
            self._print_bidding_result(board.call_history)
            self._print_hands(board.deal)
            print

    def configure_logging(self, is_verbose):
        handler = logging.StreamHandler(sys.stderr)
        formatter = logging.Formatter("%(levelname)-8s: %(message)s")
        handler.setFormatter(formatter)

        logger = logging.getLogger()
        logger.addHandler(handler)
        if is_verbose:
            logger.setLevel(logging.NOTSET)

    def main(self, args):
        self.configure_logging(True)
        args = BidderFactory.configure_from_args(args)
        bidder = BidderFactory.default_bidder()

        if "-v" in args:
            args.remove("-v")
            self.verbose = True

        if args:
            for identifier in args:
                self._bid_board(Board.from_identifier(identifier), bidder)
            return 0

        try:
            while True:
                self._bid_board(Board.random(), bidder)
        except KeyboardInterrupt:
            print
            print "User interrupted."
            return 0


if __name__ == '__main__':
    SAYCBot().main(sys.argv[1:])
