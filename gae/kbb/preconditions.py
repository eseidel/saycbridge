# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.suit import *

from kbb.handconstraints import HonorConstraint, ControlConstraint

import logging
_log = logging.getLogger(__name__)


class Precondition(object):
    def __repr__(self):
        return "%s()" % self.name()

    def name(self):
        return self.__class__.__name__

    def fits(self, knowledge, bid):
        pass


class NoOpening(Precondition):
    def fits(self, knowledge, bid):
        # Alternately: return reduce(operator.and_, map(PositionKnowledge.opened, knowledge.positions()))
        for position in knowledge.positions():
            if position.min_hcp() != 0:
                return False
        return True


class Opened(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.opened


class WeOpened(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.opened or knowledge.partner.opened


class TheyOpened(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.rho.opened or knowledge.lho.opened


class MyLastBidWasOpen(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.opening


class MyLastBidWasNotOpen(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and not knowledge.me.last_call.opening


class PartnerOpened(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.opened


class PartnerLastBidWasOpen(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.opening


class NotOpened(Precondition):
    def fits(self, knowledge, bid):
        return not knowledge.me.opened


class PartnerNotOpened(Precondition):
    def fits(self, knowledge, bid):
        return not knowledge.partner.opened


class IsNotrumpProtocol(Precondition):
    def fits(self, knowledge, bid):
        return (knowledge.me.notrump_protocol or
                knowledge.rho.notrump_protocol or
                knowledge.partner.notrump_protocol or
                knowledge.lho.notrump_protocol)


class IsSuitedProtocol(Precondition):
    def fits(self, knowledge, bid):
        return (not knowledge.me.notrump_protocol and
                not knowledge.rho.notrump_protocol and
                not knowledge.partner.notrump_protocol and
                not knowledge.lho.notrump_protocol)


class HaveBid(Precondition):
    def fits(self, knowledge, bid):
        # FIXME: This should look whether the last bid was a pass.
        return knowledge.me.last_call and not knowledge.me.last_call.is_pass()


class HaveNotBid(Precondition):
    def fits(self, knowledge, bid):
        return not knowledge.me.last_call


class RHOLastBidWasOpen(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.rho.last_call and knowledge.rho.last_call.opening


class LHOLastBidWasOpen(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.lho.last_call and knowledge.lho.last_call.opening


class RHOPassed(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.rho.last_call and knowledge.rho.last_call.is_pass()


class LHOPassed(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.rho.last_call and knowledge.rho.last_call.is_pass()


class RHOBidContract(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.rho.last_call and knowledge.rho.last_call.is_contract()


class RHODidNotBidContract(Precondition):
    def fits(self, knowledge, bid):
        return not knowledge.rho.last_call.is_contract()


class RHODoubled(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.rho.last_call.is_double()


class RHODidNotDouble(Precondition):
    def fits(self, knowledge, bid):
        return not knowledge.rho.last_call.is_double()


class RHOBidWasArtificial(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.rho.last_call and knowledge.rho.last_call.artificial


class NotBalancingSeat(Precondition):
    def fits(self, knowledge, bid):
        return not knowledge.is_balancing()


class BalancingSeat(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.is_balancing()


class FourthSeat(Precondition):
    def fits(self, knowledge, bid):
        return (knowledge.rho.last_call and knowledge.rho.last_call.is_pass() and
                knowledge.partner.last_call and knowledge.partner.last_call.is_pass() and
                knowledge.lho.last_call and knowledge.lho.last_call.is_pass())


class PartnerBid(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and not knowledge.partner.last_call.is_pass()


# WARNING! You probably want to use a more semantic precondition!
class PartnerLastNaturalSuitIn(Precondition):
    def __init__(self, expected_suits):
        # This can include NOTRUMP
        self.expected_suits = expected_suits

    def fits(self, knowledge, bid):
        partner_bid = knowledge.partner.last_call
        return partner_bid and partner_bid.is_contract() and partner_bid.strain in self.expected_suits and not partner_bid.artificial


class PartnerLastBidWasBlackwood(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.blackwood


class PartnerLastBidWasGerber(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.gerber


class PartnerLastBidWasFourthSuitForcing(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.fourth_suit_forcing


class PartnerLastBidWasMichaels(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.michaels_cuebid


class PartnerLastBidWasMichaelsMinorRequest(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.michaels_minor_request


class PartnerLastBidWasWaiting(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.name == '2D'


class PartnerLastBidWasPreemptive(Precondition):
    def fits(self, knowledge, bid):
        partner_bid = knowledge.partner.last_call
        return partner_bid and partner_bid.preempt


class PartnerLastBidWasNotPreemptive(Precondition):
    def fits(self, knowledge, bid):
        partner_bid = knowledge.partner.last_call
        return partner_bid and not partner_bid.preempt


class PartnerLastBidWasTwoNotrumpFeatureRequest(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.two_nt_feature_request


# FIXME: This may be semantically incorrect.  We should proably match against partner length instead of suit.
class PartnerLastBidWasNaturalSuit(PartnerLastNaturalSuitIn):
    def __init__(self):
        # FIXME: This will incorrectly match artificial suit bids (like cuebids, ace-asking responses, etc.)
        PartnerLastNaturalSuitIn.__init__(self, SUITS)


# FIXME: This may be semantically incorrect.  We should proably match against partner length instead of suit.
class PartnerLastBidWasNaturalMajor(PartnerLastNaturalSuitIn):
    def __init__(self):
        # FIXME: This will incorrectly match artificial suit bids (like cuebids, ace-asking responses, etc.)
        PartnerLastNaturalSuitIn.__init__(self, MAJORS)


# FIXME: This may be semantically incorrect.  We should proably match against partner length instead of suit.
class PartnerLastBidWasNaturalMinor(PartnerLastNaturalSuitIn):
    def __init__(self):
        # FIXME: This will incorrectly match artificial suit bids (like cuebids, ace-asking responses, etc.)
        PartnerLastNaturalSuitIn.__init__(self, MINORS)


class PartnerLastBidWasNaturalNotrump(Precondition):
    def fits(self, knowledge, bid):
        partner_last_call = knowledge.partner.last_call
        return partner_last_call and partner_last_call.strain == NOTRUMP and not partner_last_call.artificial


class PartnerLastBidWasContract(Precondition):
    def fits(self, knowledge, bid):
        partner_last_call = knowledge.partner.last_call
        return partner_last_call and partner_last_call.is_contract()


class PartnerLastBidWasTakeoutDouble(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.takeout_double


class MyLastBidWasBlackwood(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.blackwood


class MyLastBidWasGerber(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.gerber


class MyLastBidWasTakeoutDouble(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.takeout_double


class MyLastBidWasNegativeDouble(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.negative_double


class MyLastBidWasPreemptive(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.preempt


class PartnerLastBidWasTransfer(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.transfer_to is not None


class PartnerLastBidWasJacobyTransfer(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.jacoby_transfer


class MyLastBidWasJacobyTransfer(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.jacoby_transfer


class PartnerLastBidWasTwoSpadesPuppet(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.two_spades_puppet


class MyLastBidWasTwoSpadesPuppet(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.two_spades_puppet


class PartnerLastBidWasStayman(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.stayman


class MyLastBidWasStayman(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.me.last_call and knowledge.me.last_call.stayman


class PartnerLastBidWasJacoby2N(Precondition):
    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.jacoby_two_nt


# This means that we've already shown this many points, not that our hand has this many.
class MinimumHighCardPoints(Precondition):
    def __init__(self, min_hcp):
        self.min_hcp = min_hcp

    def fits(self, knowledge, bid):
        return knowledge.me.min_hcp() >= self.min_hcp


class MaxShownCount(Precondition):
    def __init__(self, max_count, suit=None):
        self.max_count = max_count
        self._suit = suit

    def fits(self, knowledge, bid):
        suit = bid.strain if self._suit is None else self._suit
        return knowledge.me.min_length(suit) <= self.max_count


class PartnerMinimumHighCardPoints(Precondition):
    def __init__(self, min_hcp):
        self.min_hcp = min_hcp

    def fits(self, knowledge, bid):
        return knowledge.partner.min_hcp() >= self.min_hcp


class PartnerMaxiumHighCardPoints(Precondition):
    def __init__(self, max_hcp):
        self.max_hcp = max_hcp

    def fits(self, knowledge, bid):
        return knowledge.partner.max_hcp() <= self.max_hcp


class PartnerWeak(PartnerMaxiumHighCardPoints):
    def __init__(self):
        PartnerMaxiumHighCardPoints.__init__(self, 11)


class PartnerHasAtLeastCountInSuit(Precondition):
    def __init__(self, min_count, suit=None):
        self._min_count = min_count
        self._suit = suit

    def fits(self, knowledge, bid):
        suit = bid.strain if self._suit is None else self._suit
        return suit in SUITS and knowledge.partner.min_length(suit) >= self._min_count


class UnsupportedSuit(Precondition):
    def __init__(self, suit=None):
        self._suit = suit

    def fits(self, knowledge, bid):
        suit = bid.strain if self._suit is None else self._suit
        return suit in SUITS and knowledge.partner.min_length(suit) == 0


class SecondRoundControlIsNotKnown(Precondition):
    def __init__(self, suit=None):
        self._suit = suit

    def fits(self, knowledge, bid):
        suit = bid.strain if self._suit is None else self._suit
        if suit not in SUITS:
            return

        return (knowledge.partner.control_for_round(suit, ControlConstraint.SECOND_ROUND) is None
             and knowledge.me.control_for_round(suit, ControlConstraint.SECOND_ROUND) is None)


class FitEstablishedInSomeSuit(Precondition):
    def fits(self, knowledge, bid):
        for suit in SUITS:
            if knowledge.partner.min_length(suit) + knowledge.me.min_length(suit) >= 8:
                return True
        return False


class NoFitEstablished(Precondition):
    def fits(self, knowledge, bid):
        for suit in SUITS:
            if knowledge.partner.min_length(suit) + knowledge.me.min_length(suit) >= 8:
                return False
        return True


class NotSuitWithFit(Precondition):
    def __init__(self, suit=None):
        self._suit = suit

    def fits(self, knowledge, bid):
        suit = bid.strain if self._suit is None else self._suit
        return suit in SUITS and (knowledge.partner.min_length(suit) + knowledge.me.min_length(suit) < 8)


class JumpOrHaveFit(Precondition):
    def __init__(self):
        self._fit_established = FitEstablishedInSomeSuit()
        self._is_jump = JumpFromLastContract()

    def fits(self, knowledge, bid):
        return self._fit_established.fits(knowledge, bid) or self._is_jump.fits(knowledge, bid)


class MinimumCombinedCountWithPartnersLastSuit(Precondition):
    def __init__(self, min_count):
        self._min_count = min_count

    def fits(self, knowledge, bid):
        suit = knowledge.partner.last_call.strain
        return suit in SUITS and (knowledge.partner.min_length(suit) + knowledge.me.min_length(suit)) >= self._min_count


# FIXME: Most callers probably want to know if this is a NT auction or not.
class LastBidWasSuit(Precondition):
    def __init__(self, in_suits=None):
        self._suits = in_suits or SUITS

    def fits(self, knowledge, bid):
        last_non_pass = knowledge.last_non_pass()
        return last_non_pass and last_non_pass.strain in self._suits


class LastBidWasNaturalSuit(Precondition):
    def fits(self, knowledge, bid):
        last_non_pass = knowledge.last_non_pass()
        return last_non_pass and last_non_pass.strain in SUITS and not last_non_pass.artificial


class LastBidWasNotrump(Precondition):
    def fits(self, knowledge, bid):
        last_non_pass = knowledge.last_non_pass()
        return last_non_pass and last_non_pass.strain == NOTRUMP


class RebidSameSuit(Precondition):
    def fits(self, knowledge, bid):
        if bid.strain not in SUITS:
            return False
        return knowledge.me.last_call and bid.strain == knowledge.me.last_call.strain


class NotRebidSameSuit(Precondition):
    def fits(self, knowledge, bid):
        if bid.strain not in SUITS:
            return False
        return knowledge.me.last_call and bid.strain != knowledge.me.last_call.strain


class LastBidWasLevel(Precondition):
    def __init__(self, expected_level):
        self.expected_level = expected_level

    def fits(self, knowledge, bid):
        last_non_pass = knowledge.last_non_pass()
        return last_non_pass and last_non_pass.level() == self.expected_level


# WARNING! You probably want to use a more semantic precondition!
class LastBidWas(Precondition):
    def __init__(self, expected_bid_name):
        self.expected_bid_name = expected_bid_name

    def fits(self, knowledge, bid):
        last_non_pass = knowledge.last_non_pass()
        return last_non_pass and last_non_pass.name == self.expected_bid_name


class LastBidWasByOpponents(Precondition):
    def fits(self, knowledge, bid):
        if knowledge.rho.last_call and not knowledge.rho.last_call.is_pass():
            return True
        if (knowledge.rho.last_call and
            knowledge.rho.last_call.is_pass() and
            knowledge.partner.last_call and
            knowledge.partner.last_call.is_pass() and
            knowledge.lho.last_call and
            not knowledge.lho.last_call.is_pass()):
            return True
        return False


class LastBidWasPreemptive(Precondition):
    def fits(self, knowledge, bid):
        last_non_pass = knowledge.last_non_pass()
        return last_non_pass and last_non_pass.preempt


class LastBidWasNotPreemptive(Precondition):
    def fits(self, knowledge, bid):
        last_non_pass = knowledge.last_non_pass()
        return last_non_pass and not last_non_pass.preempt


# WARNING! You probably want to use a more semantic precondition!
class PartnerLastBidWas(Precondition):
    def __init__(self, expected_bid_name):
        self.expected_bid_name = expected_bid_name

    def fits(self, knowledge, bid):
        partner_bid = knowledge.partner.last_call
        return partner_bid and partner_bid.name == self.expected_bid_name


# WARNING! You probably want to use a more semantic precondition!
class MyLastBidWas(Precondition):
    def __init__(self, expected_bid_name):
        self.expected_bid_name = expected_bid_name

    def fits(self, knowledge, bid):
        my_bid = knowledge.me.last_call
        return my_bid and my_bid.name == self.expected_bid_name


class MyLastBidWasOneOfASuit(Precondition):
    def fits(self, knowledge, bid):
        last_call = knowledge.me.last_call
        return last_call and last_call.level() == 1 and last_call.strain in SUITS


class PartnerLastBidWasLevel(Precondition):
    def __init__(self, expected_level):
        self.expected_level = expected_level

    def fits(self, knowledge, bid):
        return knowledge.partner.last_call and knowledge.partner.last_call.level() == self.expected_level


class CuebidOfRHOsSuit(Precondition):
    def fits(self, knowledge, bid):
        length, rho_suit = sorted([(knowledge.rho.min_length(suit), suit) for suit in SUITS])[-1]
        # FIXME: This will be confused by takeout doubles.
        return length >= 3 and bid.strain == rho_suit


class CuebidOfLHOsSuit(Precondition):
    def fits(self, knowledge, bid):
        length, lho_suit = sorted([(knowledge.lho.min_length(suit), suit) for suit in SUITS])[-1]
        # FIXME: This will be confused by takeout doubles.
        return length >= 3 and bid.strain == lho_suit


class SameSuitAsLastContract(Precondition):
    def fits(self, knowledge, bid):
        assert bid.strain in SUITS
        return knowledge.last_contract().strain == bid.strain


class NotSameSuitAsLastContract(Precondition):
    def fits(self, knowledge, bid):
        assert bid.strain in SUITS
        return knowledge.last_contract().strain != bid.strain


class UnbidSuit(Precondition):
    def fits(self, knowledge, bid):
        return bid.strain in knowledge.unbid_suits()


class PartnershipBidSuit(Precondition):
    def fits(self, knowledge, bid):
        return bid.strain in SUITS and bid.strain not in knowledge.our_unbid_suits()


class MinUnbidSuitCount(Precondition):
    def __init__(self, min_unbid_count):
        self._min_unbid_count = min_unbid_count

    def fits(self, knowledge, bid):
        return len(knowledge.unbid_suits()) >= self._min_unbid_count


class OnlyPartnershipUnbidSuit(UnbidSuit):
    def fits(self, knowledge, bid):
        if bid.strain not in SUITS:
            return False

        # This constraint is only used by FourthSuitForcing.
        # FIXME: This is a hack to prevent 3H over 1D,P,1S,P,2C,P,2H,P,3C,P being FSF (again).
        positions = (knowledge.me, knowledge.partner)
        for position in positions:
            if position.last_call and position.last_call.fourth_suit_forcing:
                return False

        unbid_suits = knowledge.our_unbid_suits()
        return len(unbid_suits) == 1 and unbid_suits[0] == bid.strain


class IsPass(Precondition):
    def fits(self, knowledge, bid):
        return bid.is_pass()


class ForcedToBid(Precondition):
    def _rho_bid(self, knowledge):
        return knowledge.rho.last_call and not knowledge.rho.last_call.is_pass()

    def _partner_doubled_for_penalty(self, knowledge):
        return knowledge.partner.last_call and knowledge.partner.last_call.penalty_double

    def _partner_has_passed(self, knowledge):
        return knowledge.partner.last_call and knowledge.partner.last_call.is_pass()

    def _partner_last_call_was_artificial(self, knowledge):
        return knowledge.partner.last_call and knowledge.partner.last_call.artificial

    def _is_forced_to_bid(self, knowledge):
        # FIXME: This should be covered by the hcp_is_unbounded check, except in cases where we fail to understand the pass.
        if self._partner_has_passed(knowledge):
            return False
        # Penalty doubles are never forcing, even if partner is unbounded.
        if self._partner_doubled_for_penalty(knowledge):
            return False
        if self._rho_bid(knowledge):
            return False
        # Artificial bids are always forcing.  We use explicit pass rules to convert them into natural bids.
        return knowledge.partner.hcp_is_unbounded() or self._partner_last_call_was_artificial(knowledge)

    def fits(self, knowledge, bid):
        return self._is_forced_to_bid(knowledge)


class NotForcedToBid(ForcedToBid):
    def fits(self, knowledge, bid):
        return not self._is_forced_to_bid(knowledge)


class RaiseOfPartnersLastSuit(Precondition):
    def fits(self, knowledge, bid):
        partner_last_call_suit = knowledge.partner.last_call.strain
        if partner_last_call_suit not in SUITS:
            return False
        return bid.strain == partner_last_call_suit and knowledge.partner.min_length(partner_last_call_suit) >= 3


class NotRaiseOfPartnersLastSuit(Precondition):
    def fits(self, knowledge, bid):
        # I know of no artificial passes or doubles which act as raises.
        if not bid.is_contract():
            return True

        if bid.strain not in SUITS:
            return True

        partner_bid = knowledge.partner.last_call
        if not partner_bid.artificial:
            return bid.strain != partner_bid.strain

        # FIXME: This will match earlier bids by partner, if partner's last bid was artificial
        # (for example, it will say we're raising FSF if we previously showed support).
        # FIXME: We could instead of an list of artificial raises here. (Like Jacobs2N).
        return bid.strain == partner_bid.strain or knowledge.partner.min_length(bid.strain) < 3


# FIXME: Callers could combine this with IsSuit()
class SuitHigherThanMyLastSuit(Precondition):
    def fits(self, knowledge, bid):
        if bid.strain not in SUITS:
            return False
        last_call = knowledge.me.last_call
        if last_call.strain not in SUITS:
            return False
        return bid.strain > last_call.strain


class SuitLowerThanMyLastSuit(Precondition):
    def fits(self, knowledge, bid):
        if bid.strain not in SUITS:
            return False
        last_call = knowledge.me.last_call
        if last_call.strain not in SUITS:
            return False
        return bid.strain < last_call.strain


class MinLevel(Precondition):
    def __init__(self, min_level):
        self.min_level = min_level

    def fits(self, knowledge, bid):
        if bid.is_double():
            return knowledge.last_contract().level() >= self.min_level
        return bid.is_contract() and bid.level() >= self.min_level


class MaxLevel(Precondition):
    def __init__(self, max_level):
        self.max_level = max_level

    def fits(self, knowledge, bid):
        if bid.is_double():
            return knowledge.last_contract().level() <= self.max_level
        return bid.is_contract() and bid.level() <= self.max_level


class Level(Precondition):
    def __init__(self, level):
        self._level = level

    def fits(self, knowledge, bid):
        if bid.is_double():
            return knowledge.last_contract().level() == self._level
        return bid.is_contract() and bid.level() == self._level


class IsGame(Precondition):
    def _game_level(self, suit):
        if suit in MINORS:
            return 5
        if suit in MAJORS:
            return 4
        return 3

    def fits(self, knowledge, bid):
        return bid.is_contract() and bid.level() == self._game_level(bid.strain)


class LastBidWasGameOrAbove(IsGame):
    def fits(self, knowledge, bid):
        last_contract = knowledge.last_contract()
        return last_contract.level() >= self._game_level(last_contract.strain)


class LastBidWasBelowGame(IsGame):
    def fits(self, knowledge, bid):
        last_contract = knowledge.last_contract()
        return last_contract.level() < self._game_level(last_contract.strain)


class BelowGame(IsGame):
    def fits(self, knowledge, bid):
        return bid.is_contract() and bid.level() < self._game_level(bid.strain)


class GameOrBelow(IsGame):
    def fits(self, knowledge, bid):
        return bid.is_contract() and bid.level() <= self._game_level(bid.strain)


class IsSuit(Precondition):
    def __init__(self, specific_suit=None):
        self.specific_suit = specific_suit

    def fits(self, knowledge, bid):
        if self.specific_suit is not None:
            return  bid.strain == self.specific_suit
        return bid.is_contract() and bid.strain in SUITS


class IsMinor(Precondition):
    def fits(self, knowledge, bid):
        return bid.is_contract() and bid.strain in MINORS


class IsMajor(Precondition):
    def fits(self, knowledge, bid):
        return bid.is_contract() and bid.strain in MAJORS


class IsNotrump(Precondition):
    def fits(self, knowledge, bid):
        return bid.is_contract() and bid.strain == NOTRUMP


class IsDouble(Precondition):
    def fits(self, knowledge, bid):
        return bid.is_double()


class Jump(Precondition):
    def __init__(self, exact_size=None):
        self.exact_size = exact_size

    def _jump_size(self, last_call, bid):
        if bid.strain <= last_call.strain:
            # If the new suit is less than the last bid one, than we need to change more than one level for it to be a jump.
            return bid.level() - last_call.level() - 1
        # Otherwise any bid not at the current level is a jump.
        return bid.level() - last_call.level()

    def fits(self, knowledge, bid):
        if bid.is_pass():
            return False
        if bid.is_double() or bid.is_redouble():
            bid = knowledge.last_contract()

        last_call = self._last_call(knowledge)
        if not last_call or not last_call.is_contract():  # If we don't have a previous bid to compare to, this can't be a jump.
            return False
        jump_size = self._jump_size(last_call, bid)
        if self.exact_size is None:
            return jump_size != 0
        return self.exact_size == jump_size

    def _last_call(self, knowledge):
        raise NotImplementedError


class JumpFromLastContract(Jump):
    def _last_call(self, knowledge):
        return knowledge.last_contract()


class JumpFromMyLastBid(Jump):
    def _last_call(self, knowledge):
        return knowledge.me.last_call


class JumpFromPartnerLastBid(Jump):
    def _last_call(self, knowledge):
        return knowledge.partner.last_call


class NotJumpFromLastContract(JumpFromLastContract):
    def __init__(self):
        Jump.__init__(self, exact_size=0)


class NotJumpFromMyLastBid(JumpFromMyLastBid):
    def __init__(self):
        JumpFromMyLastBid.__init__(self, exact_size=0)


class NotJumpFromPartnerLastBid(JumpFromPartnerLastBid):
    def __init__(self):
        JumpFromPartnerLastBid.__init__(self, exact_size=0)


class SameLevelAsLastContract(Precondition):
    def fits(self, knowledge, bid):
        if not bid.is_contract():
            return False
        last_contract = knowledge.last_contract()
        return last_contract and last_contract.level() == bid.level()


class MinimumCombinedPointsPrecondition(Precondition):
    def __init__(self, min_points):
        self.min_points = min_points

    def fits(self, knowledge, bid):
        return knowledge.partner.min_hcp() + knowledge.me.min_hcp() >= self.min_points
