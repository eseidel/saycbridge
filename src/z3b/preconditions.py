# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from third_party import enum
import core.suit as suit


annotations = enum.Enum(
    "Opening",
    "NoTrumpSystemsOn",
    "Artificial",
    "Stayman",
    "Gerber",
    "Transfer",
    "NegativeDouble",
    "Jacoby2N",
    "TakeoutDouble",
    "MichaelsCuebid",
    "Unusual2N",
)


class Precondition(object):
    def __repr__(self):
        return "%s()" % self.name

    @property
    def name(self):
        return self.__class__.__name__

    def fits(self, history, call):
        raise NotImplementedError


class InvertedPrecondition(Precondition):
    def __init__(self, precondition):
        self.precondition = precondition

    @property
    def name(self):
        return "NOT_%s" % self.precondition.name

    def fits(self, history, call):
        return not self.precondition.fits(history, call)


class NoOpening(Precondition):
    def fits(self, history, call):
        return annotations.Opening not in history.annotations


class Opened(Precondition):
    def __init__(self, position):
        self.position = position

    def fits(self, history, call):
        return annotations.Opening in history.annotations_for_position(self.position)


class HasNotBid(Precondition):
    def __init__(self, position):
        self.position = position

    def fits(self, history, call):
        for view in history.view_for(self.position).walk:
            if view.last_call and not view.last_call.is_pass():
                return False
        return True


class ForcedToBid(Precondition):
    def _rho_bid(self, history):
        return history.rho.last_call and not history.rho.last_call.is_pass()

    def _partner_last_bid_was_pass(self, history):
        return history.partner.last_call and history.partner.last_call.is_pass()

    def _partner_last_call_was_artificial(self, history):
        return annotations.Artificial in history.partner.annotations_for_last_call

    def _is_forced_to_bid(self, history):
        # If partner hasn't bid yet then cannot be forcing
        if history.partner.last_call is None:
            return False
        if self._partner_last_bid_was_pass(history):
            return False
        # FIXME: Understand penalty doubles.
        if self._rho_bid(history):
            return False
        # Artificial bids are always forcing. We use explicit pass rules to convert them into natural bids.
        if self._partner_last_call_was_artificial(history):
            return True
        # FIXME: We're attempting to express that partner is unbounded but
        # partner is never truly unbounded if other players have bid.
        # "Game is not remote" might be better?
        return history.partner.could_have_more_points_than(17)

    def fits(self, history, call):
        return self._is_forced_to_bid(history)


class LastBidHasAnnotation(Precondition):
    def __init__(self, position, annotation):
        self.position = position
        self.annotation = annotation

    def __repr__(self):
        return "%s(%s, %s)" % (self.name, repr(self.position.key), repr(self.annotation.key))

    def fits(self, history, call):
        return self.annotation in history.view_for(self.position).annotations_for_last_call


class LastBidHasStrain(Precondition):
    def __init__(self, position, strain_or_strains):
        self.position = position
        if strain_or_strains in suit.STRAINS:
            self.strains = [strain_or_strains]
        else:
            self.strains = strain_or_strains

    def __repr__(self):
        return "%s(%s, %s)" % (self.name, repr(self.position.key), self.strains)

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.strain in self.strains


class LastBidHasSuit(Precondition):
    def __init__(self, position=None):
        self.position = position

    def __repr__(self):
        return "%s(%s)" % (self.name, repr(self.position.key))

    def fits(self, history, call):
        last_call = history.last_contract if not self.position else history.view_for(self.position).last_call
        return last_call and last_call.strain in suit.SUITS


class LastBidHasLevel(Precondition):
    def __init__(self, position, level):
        self.position = position
        self.level = level

    def __repr__(self):
        return "%s(%s, %s)" % (self.name, repr(self.position.key), self.level)

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.level() == self.level


class LastBidWas(Precondition):
    def __init__(self, position, call_name):
        self.position = position
        self.call_name = call_name

    def __repr__(self):
        return "%s(%s, %s)" % (self.name, repr(self.position.key), self.call_name)

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.name == self.call_name


class RaiseOfPartnersLastSuit(Precondition):
    def fits(self, history, call):
        partner_last_call = history.partner.last_call
        if not partner_last_call or partner_last_call.strain not in suit.SUITS:
            return False
        return call.strain == partner_last_call.strain and history.partner.min_length(partner_last_call.strain) >= 3


class SuitLowerThanMyLastSuit(Precondition):
    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        last_call = history.me.last_call
        if last_call.strain not in suit.SUITS:
            return False
        return call.strain < last_call.strain


class RebidSameSuit(Precondition):
    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return history.me.last_call and call.strain == history.me.last_call.strain


class PartnerHasAtLeastLengthInSuit(Precondition):
    def __init__(self, length):
        self.length = length

    def __repr__(self):
        return "%s(%s)" % (self.name, self.length)

    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return history.partner.min_length(call.strain) >= self.length


class UnbidSuit(Precondition):
    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return history.is_unbid_suit(call.strain)


class MinUnbidSuitCount(Precondition):
    def __init__(self, count):
        self.count = count

    def fits(self, history, call):
        return len(history.unbid_suits) >= self.count


class Strain(Precondition):
    def __init__(self, strain):
        self.strain = strain

    def __repr__(self):
        return "%s(%s)" % (self.name, self.strain)

    def fits(self, history, call):
        return call.strain == self.strain


class MaxLevel(Precondition):
    def __init__(self, max_level):
        self.max_level = max_level

    def fits(self, history, call):
        if call.is_double():
            return history.last_contract.level() <= self.max_level
        return call.is_contract() and call.level() <= self.max_level


class MinimumCombinedPointsPrecondition(Precondition):
    def __init__(self, min_points):
        self.min_points = min_points

    def fits(self, history, call):
        return history.partner.min_points + history.me.min_points >= self.min_points


class Jump(Precondition):
    def __init__(self, exact_size=None):
        self.exact_size = exact_size

    def _jump_size(self, last_call, call):
        if call.strain <= last_call.strain:
            # If the new suit is less than the last bid one, than we need to change more than one level for it to be a jump.
            return call.level() - last_call.level() - 1
        # Otherwise any bid not at the current level is a jump.
        return call.level() - last_call.level()

    def fits(self, history, call):
        if call.is_pass():
            return False
        if call.is_double() or call.is_redouble():
            call = history.call_history.last_contract()

        last_call = self._last_call(history)
        if not last_call or not last_call.is_contract():  # If we don't have a previous bid to compare to, this can't be a jump.
            return False
        jump_size = self._jump_size(last_call, call)
        if self.exact_size is None:
            return jump_size != 0
        return self.exact_size == jump_size

    def _last_call(self, history):
        raise NotImplementedError


class JumpFromLastContract(Jump):
    def _last_call(self, history):
        return history.call_history.last_contract()


class JumpFromMyLastBid(Jump):
    def _last_call(self, history):
        return history.me.last_call


class JumpFromPartnerLastBid(Jump):
    def _last_call(self, history):
        return history.partner.last_call


class NotJumpFromLastContract(JumpFromLastContract):
    def __init__(self):
        JumpFromLastContract.__init__(self, exact_size=0)


class NotJumpFromMyLastBid(JumpFromMyLastBid):
    def __init__(self):
        JumpFromMyLastBid.__init__(self, exact_size=0)


class NotJumpFromPartnerLastBid(JumpFromPartnerLastBid):
    def __init__(self):
        JumpFromPartnerLastBid.__init__(self, exact_size=0)
