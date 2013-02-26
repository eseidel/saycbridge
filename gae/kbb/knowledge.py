import collections

from third_party import enum

from kbb.handconstraints import HandConstraints, HonorConstraint
from core.call import Call
from core.suit import suit_char, SUITS, MINORS, MAJORS
from core.position import NORTH, rho_of, partner_of, lho_of

import logging
_log = logging.getLogger(__name__)


point_systems = enum.Enum(
    "HighCardPoints", # Should be default.
    "LengthPoints",
    "SupportPointsIfFit", # Trump-length dependent short-suit bonus, non-working honors adjustment.  If no fit, LengthPoints.
    # FIXME: NotrumpSupport currently does not affect any results, but I expect it will in the future.
    # We can try removing it later and if it doesn't break anything, just kill it.
    "NotrumpSupport", # return hand.high_card_points() - 1 if hand.is_flat() else hand.high_card_points()
)


# Knowledege is always from the perspective of a single player.
# When building knowledge objects we rotate them to represent the
# perspective from the current player, as all Rule objects are
# written from the perspective of the current player.
# When constructing knowledge we may use a different set of
# rules for our partnership vs. theirs.
class Knowledge(object):
    def __init__(self):
        self._last_contract = None
        self.me = PositionKnowledge()
        self.rho = PositionKnowledge()
        self.partner = PositionKnowledge()
        self.lho = PositionKnowledge()
        # FIXME: May need some sort of self.us and self.them objects
        # which store things like self.notrump_auction.
        # One partnership may be doing a NT auction, while another is doing suits
        # in the case of a NT overcall.

    def rotate(self):
        if self.me.last_call.is_contract():
            self._last_contract = self.me.last_call

        old_me = self.me
        self.me = self.lho
        self.lho = self.partner
        self.partner = self.rho
        self.rho = old_me

    def pretty_one_line(self):
        return "me: %s partner: %s lho %s rho: %s" % (self.me, self.partner, self.lho, self.rho)

    def __str__(self):
        return self.pretty_one_line()

    # FIXME: Probably want us() and them() which return combined knowledge
    # It's unclear if those would just be another HandConstraints object
    # or some sort of PartnershipConstraints with additional accessors?

    def _previous_positions(self):
        return [self.rho, self.partner, self.lho, self.me]

    def positions(self):
        return [self.me, self.rho, self.partner, self.lho]


    # Knowledge doesn't know anything about positions, but given a reference point it can generate a standard NESW list.
    def absolute_positions(self, me_position=None):
        if me_position is None:
            me_position = NORTH
        positions = [None, None, None, None]
        positions[me_position] = self.me
        positions[rho_of(me_position)] = self.rho
        positions[lho_of(me_position)] = self.lho
        positions[partner_of(me_position)] = self.partner
        return positions

    def last_contract(self):
        return self._last_contract

    def last_non_pass(self):
        # This will return doubles and redoubles in addition to contract bids.
        for position in self._previous_positions():
            if position.last_call and not position.last_call.is_pass():
                return position.last_call
        return None

    def is_balancing(self):
        # True if last bid from rho() and partner() was "pass". If they've not bid at all, they'll get a chance.
        if not self.lho.last_call:
            return False
        if not self.rho.last_call or not self.rho.last_call.is_pass():
            return False
        return self.partner.last_call and self.partner.last_call.is_pass()

    # FIXME: Unclear if this belongs on knowledge.  The concept of being "bid" vs. not may be system dependent.
    # For example, does a negative double count as "bidding" the unmentioned major?  Depends on the context.
    def unbid_suits(self):
        return filter(self.is_unbid_suit, SUITS)

    def our_unbid_suits(self):
        unbid_by_us = lambda suit: not self.me.did_bid_suit(suit) and not self.partner.did_bid_suit(suit)
        return filter(unbid_by_us, SUITS)

    def their_bid_suits(self):
        bid_by_them = lambda suit: self.rho.did_bid_suit(suit) or self.lho.did_bid_suit(suit)
        return filter(bid_by_them, SUITS)

    def is_unbid_suit(self, suit):
        assert suit in SUITS
        for position in self.positions():
            if position.did_bid_suit(suit):
                return False
        return True


# FIXME: Merge with HandConstraints.
class PositionKnowledge(HandConstraints):
    def __init__(self):
        HandConstraints.__init__(self)
        self.last_call = None
        self.opened = False
        self.notrump_protocol = False
        self.rule_of_twenty = None
        self.rule_of_fifteen = None

    def did_bid_suit(self, suit):
        assert suit in SUITS
        did_bid_length = 4 # Showing 4 cards in the suit is consider bidding it, except for 1C.
        # FIXME: This is all a big hack to avoid treating the last takeout double as having "bid" a minor
        # yet allowing 1C to only show 3.
        if suit in MINORS and self.last_call and self.last_call.name != 'X':
            did_bid_length = 3
        if self.min_length(suit) >= did_bid_length:
            return True
        # FIXME: This is a hack to make sure we default to treating nonsense bids as natural?
        if self.last_call and not self.last_call.artificial and self.last_call.strain == suit:
            return True
        return False

    def forget_everything(self):
        PositionKnowledge.__init__(self)

    def explore_string(self):
        return self.pretty_one_line(include_last_call_name=False)

    def pretty_one_line(self, include_last_call_name=True):
        pretty_line = HandConstraints.pretty_one_line(self)
        if self.last_call or self.opened:
            info_strings = []
            if include_last_call_name:
                info_strings.append("last: %s" % self.last_call)
            else:
                last_call_string = self.last_call.pretty_one_line(include_bid_name=False)
                if last_call_string:
                    info_strings.append(last_call_string)
            if self.opened:
                info_strings.append("opened")
            if self.notrump_protocol:
                info_strings.append("nt")
            if self.ace_constraint() is not None:
                ace_constraint = self.ace_constraint()
                ace_count = "0 or 4" if ace_constraint == HandConstraints.ZERO_OR_FOUR else str(ace_constraint)
                info_strings.append("aces(%s)" % ace_count)
            if self.king_constraint() is not None:
                king_constraint = self.king_constraint()
                king_count = "0 or 4" if king_constraint == HandConstraints.ZERO_OR_FOUR else str(king_constraint)
                info_strings.append("kings(%s)" % king_count)
            if info_strings:
                pretty_line +=" (%s)" % ", ".join(info_strings)
        return pretty_line
