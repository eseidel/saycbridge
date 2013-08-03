# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from core.call import Call
from core.suit import CLUBS, suit_char


# A wrapper around a bid object which adds some semantics.
class SemanticBid(Call):
    def __init__(self, bid_name,
            artificial=None,
            opening=None,
            transfer_to=None,
            takeout_double=None,
            negative_double=None,
            penalty_double=None,
            lead_directing_double=None,
            blackwood=None,
            gerber=None,
            michaels_cuebid=None,
            michaels_minor_request=None,
            unusual_two_nt=None,
            stayman=None,
            jacoby_two_nt=None,
            jacoby_transfer=None,
            two_spades_puppet=None,
            fourth_suit_forcing=None,
            preempt=None,
            jordan=None,
            two_nt_feature_request=None):
        Call.__init__(self, bid_name)
        self.artificial = artificial or False
        self.preempt = preempt or False
        self.opening = opening or False
        self.transfer_to = transfer_to
        self.takeout_double = takeout_double or False
        self.negative_double = negative_double or False
        self.penalty_double = penalty_double or False
        self.lead_directing_double = lead_directing_double or False
        self.blackwood = blackwood or False
        self.gerber = gerber or False
        # FIXME: Stayman could be written more generically on HandConstraints by promising a 4-card major.
        self.stayman = stayman or False
        # FIXME: Michaels could be written more generically on HandConstraints by promising a 5-card minor.
        self.michaels_cuebid = michaels_cuebid or False
        self.michaels_minor_request = michaels_minor_request or False
        # FIXME: Unusual2NT could be written more generically on HandConstraints by promising a 5-card major.
        self.unusual_two_nt = unusual_two_nt or False
        self.jacoby_two_nt = jacoby_two_nt or False
        self.jacoby_transfer = jacoby_transfer or False
        # FIXME: TwoSpadesPuppet could be written more generically on HandConstraints by promising a 6-card minor.
        self.two_spades_puppet = two_spades_puppet or False
        self.fourth_suit_forcing = fourth_suit_forcing or False
        self.two_nt_feature_request = two_nt_feature_request or False
        self.jordan = jordan or False  # Jordan doesn't really need its own flag, no one ever checks it.

    def pretty_one_line(self, include_bid_name=True):
        flag_strings = []
        if include_bid_name:
            flag_strings.append(self.name)
        if self.opening:
            flag_strings.append('opening')
        if self.takeout_double:
            flag_strings.append('takeout')
        if self.negative_double:
            flag_strings.append('negative')
        if self.lead_directing_double:
            flag_strings.append('lead_directing')
        if self.penalty_double:
            flag_strings.append('penalty')
        if self.blackwood:
            flag_strings.append('blackwood')
        if self.gerber:
            flag_strings.append('gerber')
        if self.michaels_cuebid:
            flag_strings.append('michaels')
        if self.michaels_minor_request:
            flag_strings.append('minor_request')
        if self.stayman:
            flag_strings.append('stayman')
        if self.two_spades_puppet:
            flag_strings.append('two_spades_puppet')
        if self.transfer_to:
            flag_strings.append('transfer_to=%s' % suit_char(self.transfer_to))
        if self.jacoby_transfer:
            flag_strings.append('jacoby_transfer')
        if self.fourth_suit_forcing:
            flag_strings.append('fsf')
        if self.two_nt_feature_request:
            flag_strings.append('feature_request')
        if self.jordan:
            flag_strings.append('jordan')
        if self.preempt:
            flag_strings.append('preempt')
        return " ".join(flag_strings)

    def __str__(self):
        return self.pretty_one_line()

    def __repr__(self):
        options = ''
        if self.opening:
            options += ', opening=True'
        if self.takeout_double:
            options += ', takeout_double=True'
        if self.negative_double:
            options += ', negative_double=True'
        if self.lead_directing_double:
            options += ', lead_directing_double=True'
        if self.penalty_double:
            options += ', penalty_double=True'
        if self.blackwood:
            options += ', blackwood=True'
        if self.gerber:
            options += ', gerber=True'
        if self.stayman:
            options += ', stayman=True'
        if self.two_spades_puppet:
            options += ', two_spades_puppet=True'
        if self.transfer_to:
            options += ', transfer_to=%s' % suit_char(self.transfer_to)
        if self.jacoby_transfer:
            options += ', jacoby_transfer=True'
        if self.fourth_suit_forcing:
            options += ', fourth_suit_forcing=True'
        if self.two_nt_feature_request:
            options += ', two_nt_feature_request=True'
        if self.jordan:
            options += ', jordan=True'
        if self.preempt:
            options += ', preempt=True'
        return "SemanticBid('%s'%s)" % (self.name, options)


class Stayman(SemanticBid):
    def __init__(self, bid_name):
        SemanticBid.__init__(self, bid_name, stayman=True, artificial=True)


class Opening(SemanticBid):
    def __init__(self, *args, **kwargs):
        kwargs['opening'] = True
        SemanticBid.__init__(self, *args, **kwargs)


# StrongTwoClubs happens to be artificial opening, hence it has its own class.
class StrongTwoClubs(SemanticBid):
    def __init__(self, bid_name):
        SemanticBid.__init__(self, bid_name, opening=True, artificial=True)


class OpeningPreempt(SemanticBid):
    def __init__(self, bid_name):
        SemanticBid.__init__(self, bid_name, opening=True, preempt=True)


class Preempt(SemanticBid):
    def __init__(self, bid_name):
        SemanticBid.__init__(self, bid_name, preempt=True)


# Unclear exactly what "artificial" means, currently defining any suited bid
# which says nothing about the suit bid, or any NT bid which is not to play
# as artificial.  Unclear what doubles are "artificial".
class Artificial(SemanticBid):
    def __init__(self, *args, **kwargs):
        kwargs['artificial'] = True
        SemanticBid.__init__(self, *args, **kwargs)


class Gerber(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, gerber=True)


class UnusualNotrump(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, unusual_two_nt=True)


class MichaelsCuebid(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, michaels_cuebid=True)


class MichaelsMinorRequest(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, michaels_minor_request=True)


class Blackwood(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, blackwood=True)


class NegativeDouble(SemanticBid):
    def __init__(self, bid_name):
        # FIXME: Should this be "artificial"?
        SemanticBid.__init__(self, bid_name, negative_double=True)


class TakeoutDouble(SemanticBid):
    def __init__(self, bid_name):
        # Unclear what doubles are artificial?
        SemanticBid.__init__(self, bid_name, takeout_double=True, artificial=True)


class PenaltyDouble(SemanticBid):
    def __init__(self, bid_name):
        SemanticBid.__init__(self, bid_name, penalty_double=True)


class LeadDirectingDouble(SemanticBid):
    def __init__(self, bid_name):
        # FIXME: Should this be "artificial"?
        SemanticBid.__init__(self, bid_name, lead_directing_double=True)


class TwoSpadesPuppet(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, two_spades_puppet=True, transfer_to=CLUBS)


class Jacoby2N(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, jacoby_two_nt=True)


class JacobyTransfer(Artificial):
    def __init__(self, bid_name, transfer_to):
        Artificial.__init__(self, bid_name, jacoby_transfer=True, transfer_to=transfer_to)


class FourthSuitForcing(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, fourth_suit_forcing=True)


class TwoNotrumpFeatureRequest(Artificial):
    def __init__(self, bid_name):
        Artificial.__init__(self, bid_name, two_nt_feature_request=True)


class Jordan(Artificial):
    def __init__(self, bid_name):
        # We don't really need a jordan flag, we just need to mark Jordan as artificial.
        Artificial.__init__(self, bid_name, jordan=True)
