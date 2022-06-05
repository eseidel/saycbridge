# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from builtins import object
from z3b.preconditions import annotations
from core import suit
from z3b.model import positions


# Unclear where this logic should go.  It used to live in the
# ForcedToBid precondition, but it's possible it should move to
# a call-auto-annotator system instead.  The concept of "forcing"
# is system-specific.  This logic attempts to handle the generic
# sense of "forcing" for SAYC as well as respect individual bids
# ability to opt in or out of their default "forcing" characteristic.
class SAYCForcingOracle(object):
    def _rho_bid(self, history):
        return history.rho.last_call and not history.rho.last_call.is_pass()

    def _partner_last_bid_was_pass(self, history):
        return history.partner.last_call and history.partner.last_call.is_pass()

    def _am_opener_and_partner_last_call_was_unbid_suit(self, history):
        if annotations.Opening not in history.me.annotations:
            return False
        assert annotations.Artificial not in history.partner.annotations_for_last_call
        call = history.partner.last_call
        assert call
        assert call.strain != suit.NOTRUMP
        # FIXME: We should not be using private methods on History!
        history_before_partner_last_bid = history._history_after_last_call_for(positions.LHO)
        # If partner began the bidding, than of course his bid was an unbid suit!
        if not history_before_partner_last_bid:
            return True
        return call.strain in history_before_partner_last_bid.us.unbid_suits

    def forced_to_bid(self, history):
        # If partner hasn't bid yet, he can't be forcing us to bid.
        if history.partner.last_call is None:
            return False
        if self._partner_last_bid_was_pass(history):
            return False
        if self._rho_bid(history):
            return False
        # Artificial bids are always forcing. We use explicit pass rules to convert them into natural bids.
        if annotations.Artificial in history.partner.annotations_for_last_call:
            return True
        if annotations.OpenerReverse in history.partner.annotations_for_last_call:
            return True
        # Natural NT bids are never forcing in SAYC.
        if history.partner.last_call.strain == suit.NOTRUMP:
            return False

        # This code works, but for SAYC we don't yet have any rules which need an explicit forcing=True.
        rule_for_last_call = history.partner.rule_for_last_call
        if rule_for_last_call and rule_for_last_call.forcing is not None:
            return rule_for_last_call.forcing

        # This logic assumes that doubles/redoubles are non-forcing (which is correct for penalty, wrong for takeout/negative).
        # Since takeout/negative currently have explcit response coverage, this is OK for now.
        return self._am_opener_and_partner_last_call_was_unbid_suit(history)
