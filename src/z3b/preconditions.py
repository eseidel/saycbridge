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
)


class Precondition(object):
    def __repr__(self):
        return "%s()" % self.name()

    def name(self):
        return self.__class__.__name__

    def fits(self, history, call):
        pass


class InvertedPrecondition(Precondition):
    def __init__(self, precondition):
        self.precondition = precondition

    def name(self):
        return "not" + self.precondition.name()

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


class LastBidHasAnnotation(Precondition):
    def __init__(self, position, annotation):
        self.position = position
        self.annotation = annotation

    def fits(self, history, call):
        return self.annotation in history.view_for(self.position).annotations_for_last_call


class LastBidHasStrain(Precondition):
    def __init__(self, position, strain):
        self.position = position
        self.strain = strain

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.strain == self.strain


class LastBidWas(Precondition):
    def __init__(self, position, call_name):
        self.position = position
        self.call_name = call_name

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.name == self.call_name


class RaiseOfPartnersLastSuit(Precondition):
    def fits(self, history, call):
        partner_last_call = history.partner.last_call
        if not partner_last_call or partner_last_call.strain not in suit.SUITS:
            return False
        return call.strain == partner_last_call.strain and history.partner.min_length(partner_last_call.strain) >= 3


class UnbidSuit(Precondition):
    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return history.is_unbid_suit(call.strain)


class Strain(Precondition):
    def __init__(self, strain):
        self.strain = strain

    def fits(self, history, call):
        return call.strain == self.strain


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
