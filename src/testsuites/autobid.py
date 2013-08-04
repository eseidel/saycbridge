# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest2

from core.board import Board
from core.autobidder import Autobidder


class AutobidSuite():
    # These are more integration tests. Mostly they test to make sure no exceptions are thrown.
    def test_autobid_boards(self):
        return  # We haven't validated the correct sequences for these boards yet.
        autobid_tests = [
            ['2-7659223909716611891513429323023-S:NS:', 'P 1C 1D 1N P 2C P 3C P P P'], # FIXME: Should prefer NT over the Club fit.
            ['12-1687927834866188189604681273153-N:NS:', 'P 1S P 2N P 3H P 4S P P P'], # Missing Constraints.set_max_length
            ['8-10330108089788904448408255153821-N:NO:', '1S P 2N P 3S P 4S P P P'], # Missing Constraints.set_min_hcp
            ['16-17722217102379974085163255608564-N:EW:', 'P P 1N P 2D P 3H P 3N P P P'],  # Exception during super-accept processing (this probably belongs in 3H, not game).
            ['6-18342278105234647400959417453467-S:EW:', 'P P P 1H P 2H X 4H P P P'],  # Exception when making takeout double after previous pass.
            ['3-9219987693386767128151172464170-W:EW:', 'P P 1S 2C 2S P 4S P P P'],  # Exception in SuitedOvercall constraints matching.
            ['7-2468698481284035087711785637600-W:BO:', 'P 1D P P P'],  # Another exception in SuitedOvercall constraints
            ['7-11553666070312465393548297181449-W:BO:', 'P P 1N P 2C P 2D P P P'], # A beautiful escape stayman (S probably should have bid)
            ['13-619826285776537175334034524630-E:BO', 'P P 3D 4D P 4H P P P'], # N-S should really find slam, but at least with michaels they find their heart fit!
            ['4-15619586567882385203424966520920-N:BO:', '3C P P X P 3S P 3N P P P'], # Michaels was matching after a bid from partner.
            ['9-14910876904483889711425660555578-E:EW:', '1D 1H 1S 3H P P P'], # Minimum response bidder was previously bidding at the 4 level!
            ['8-13630576522446720556439533318911-N:NO:', 'P 1H 1S 2C 3S P 4S P P P'], # Previously east tried to rebid his hearts at the 4 level.
            ['16-17025830505548653358317164187380-N:EW:', 'P P 2H X P 3S P 3N P P P'], # West's unforced 3N rebid after a takeout double is wrong.
            ['13-19553695113043696995824991346950-E:BO:', 'P P 1N P 2H P 2S P 2N P 3S P P P'], # Exception when interpreting 3S as a suit rebid.
            ['14-918359155455085678216423112934-S:NO:', '1D P 1S P 1N 2C P P P'], # Exception while matching constraints from SuitedOvercall
            ['7-1509734439981714943858663927146-W:BO:', 'P 1S P 2C P 2N P 3C P 3N P P P'], # North previously made a strange 3h bid.
            ['4-16763877125918801777768905065465-N:BO:P,P,1D,P,1S,P,2N,P,3H,P,4H,P,P,P', 'P P 1D P 1S P 2N P 3H P 4H P P P'], # This auction makes no sense, but shouldn't throw an exception.
            ['10-1820919869766253986347530789986-S:BO:', 'P P P 1C P 1D P 2N P 3C P 3S P 4S P P P'], # Exception due to bad NotrumpRebid matching logic.
            ['6-1900270765157025768477602200065-S:EW:', '1H 2H 3H 3S 4H 4S P P P'], # Bidding spun out of control.
            ['3-8695851819328337104436553070122-W:EW:', 'P P 1D P 1H P 2N P 3C P 3S P 3N P P P'], # Exception due to spade length confusion.
            ['10-7470345118006940253629716986888-S:BO:', '1H P P X P P P'], # This auction makes no sense, but NotrumpRebid was incorrectly marking S as < 4 hearts due to 1N.
        ]
        bidder = self.bidder
        for board_identifier, expected_calls_string in autobid_tests:
            board = Board.from_identifier(board_identifier)
            Autobidder(bidder).bid_all_hands(board)
            self.assertEquals(board.call_history.calls_string(), expected_calls_string)
