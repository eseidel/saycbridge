# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from z3b import enum
import core.suit as suit


# The ordering of these values does not matter.  We only use Enum so that
# python throws an lookup error when we typo the annotation name.
annotations = enum.Enum(
    "Opening",

    # FIXME: It's a bit odd that 1C, 1S, 2N can end up with both
    # OneLevelSuitOpening and NotrumpSystemsOn.
    # e.g. Does ResponderJumpShift apply after 2N?
    "OneLevelSuitOpening", # 1-level suited response opening book.
    "StrongTwoClubOpening", # 2C response opening book.
    "NotrumpSystemsOn", # NT response opening book.
    "StandardOvercall", # Overcall opening book.
    "Preemptive", # Preemptive opening book.

    "BidClubs",
    "BidDiamonds",
    "BidHearts",
    "BidSpades",

    # Not all Cappelletti bids are artificial, some can be treated as to-play.
    "Cappelletti",

    "Artificial",
    # NOTE: RuleCompiler._compile_annotations will automatically imply
    # "Artificial" when encountering any annotations > Artificial.
    # This is a hack to avoid "forgot to add Artifical" bugs.
    "Blackwood",
    "FeatureRequest",
    "FourthSuitForcing",
    "Gerber",
    "Jacoby2N",
    "MichaelsCuebid",
    "MichaelsMinorRequest",
    "CappellettiMinorRequest",
    "NegativeDouble",
    "Stayman",
    "TakeoutDouble",
    "Transfer",
    "Unusual2N",
)

# Used by RuleCompiler._compile_annotations.
implies_artificial = set([value for value in annotations if value > annotations.Artificial])


def did_bid_annotation(suit):
    return (
        annotations.BidClubs,
        annotations.BidDiamonds,
        annotations.BidHearts,
        annotations.BidSpades,
    )[suit.index]


class Precondition(object):
    repr_name = None

    def __repr__(self):
        name = self.repr_name or self.__class__.__name__
        return "%s(%s)" % (name, ", ".join(map(repr, self.repr_args)))

    @property
    def repr_args(self):
        return []

    def fits(self, history, call):
        raise NotImplementedError


class InvertedPrecondition(Precondition):
    repr_name = "Not"

    def __init__(self, precondition):
        self.precondition = precondition

    @property
    def repr_args(self):
        return [self.precondition]

    def fits(self, history, call):
        return not self.precondition.fits(history, call)


class SummaryPrecondition(Precondition):
    def __init__(self, *preconditions):
        self.preconditions = preconditions

    @property
    def repr_args(self):
        return self.preconditions


class EitherPrecondition(SummaryPrecondition):
    repr_name = "Either"

    def fits(self, history, call):
        return any(precondition.fits(history, call) for precondition in self.preconditions)


class AndPrecondition(SummaryPrecondition):
    repr_name = "And"

    def fits(self, history, call):
        return all(precondition.fits(history, call) for precondition in self.preconditions)


class NoOpening(Precondition):
    def fits(self, history, call):
        return annotations.Opening not in history.annotations


class Opened(Precondition):
    def __init__(self, position):
        self.position = position

    @property
    def repr_args(self):
        return [self.position.key]

    def fits(self, history, call):
        return annotations.Opening in history.annotations_for_position(self.position)


class TheyOpened(Precondition):
    def fits(self, history, call):
        return annotations.Opening in history.them.annotations


# FIXME: Rename to NotrumpOpeningBook?
class NotrumpSystemsOn(Precondition):
    def fits(self, history, call):
        return annotations.NotrumpSystemsOn in history.us.annotations


class OneLevelSuitedOpeningBook(Precondition):
    def fits(self, history, call):
        return annotations.OneLevelSuitOpening in history.us.annotations


class StrongTwoClubOpeningBook(Precondition):
    def fits(self, history, call):
        return annotations.StrongTwoClubOpening in history.us.annotations


class HasBid(Precondition):
    def __init__(self, position):
        self.position = position

    @property
    def repr_args(self):
        return [self.position.key]

    def fits(self, history, call):
        for view in history.view_for(self.position).walk:
            if view.last_call and not view.last_call.is_pass():
                return True
        return False


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
        # FIXME: This is a lame hack.  Natural NT bids are never forcing.
        if history.partner.last_call.strain == suit.NOTRUMP:
            return False
        # FIXME: We're attempting to express that partner is unbounded but
        # partner is never truly unbounded if other players have bid.
        # "Game is not remote" might be better?
        # FIXME: This is wrong and will cause hands with 17+ points to
        # only be able to make forcing bids, including 2N! NT is bounded and thus never forcing.
        return history.partner.could_have_more_points_than(17)

    def fits(self, history, call):
        return self._is_forced_to_bid(history)


class IsGame(Precondition):
    def _game_level(self, strain):
        if strain in suit.MINORS:
            return 5
        if strain in suit.MAJORS:
            return 4
        return 3

    def fits(self, history, call):
        return call.is_contract() and call.level == self._game_level(bid.strain)


class LastBidWasBelowGame(IsGame):
    def fits(self, history, call):
        last_contract = history.last_contract
        return last_contract.level < self._game_level(last_contract.strain)


class LastBidWasGameOrAbove(IsGame):
    def fits(self, history, call):
        last_contract = history.last_contract
        return last_contract.level >= self._game_level(last_contract.strain)


class LastBidWasBelowSlam(Precondition):
    def fits(self, history, call):
        last_contract = history.last_contract
        return last_contract.level < 6


class LastBidHasAnnotation(Precondition):
    def __init__(self, position, annotation):
        self.position = position
        self.annotation = annotation
        # This assert is likely incompatible with module based development, but is nice for catching typos.
        assert self.annotation in annotations

    @property
    def repr_args(self):
        return [self.position.key, self.annotation.key]

    def fits(self, history, call):
        return self.annotation in history.view_for(self.position).annotations_for_last_call


class LastBidHasStrain(Precondition):
    def __init__(self, position, strain_or_strains):
        self.position = position
        if strain_or_strains in suit.STRAINS:
            self.strains = [strain_or_strains]
        else:
            self.strains = strain_or_strains

    @property
    def repr_args(self):
        return [self.position.key, self.strains]

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.strain in self.strains


class LastBidHasSuit(Precondition):
    def __init__(self, position=None):
        self.position = position

    @property
    def repr_args(self):
        position_string = repr(self.position.key) if self.position else None
        return [position_string]

    def fits(self, history, call):
        last_call = history.last_contract if not self.position else history.view_for(self.position).last_call
        return last_call and last_call.strain in suit.SUITS


class LastBidHasLevel(Precondition):
    def __init__(self, position, level):
        self.position = position
        self.level = level

    @property
    def repr_args(self):
        return [self.position.key, self.level]

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.level == self.level


class LastBidWas(Precondition):
    def __init__(self, position, call_name):
        self.position = position
        self.call_name = call_name

    @property
    def repr_args(self):
        return [self.position.key, self.call_name]

    def fits(self, history, call):
        last_call = history.view_for(self.position).last_call
        return last_call and last_call.name == self.call_name


class RaiseOfPartnersLastSuit(Precondition):
    def fits(self, history, call):
        partner_last_call = history.partner.last_call
        if not partner_last_call or partner_last_call.strain not in suit.SUITS:
            return False
        return call.strain == partner_last_call.strain and history.partner.min_length(partner_last_call.strain) >= 3


class CueBid(Precondition):
    def __init__(self, position, use_first_suit=False):
        self.position = position
        self.use_first_suit = use_first_suit

    def fits(self, history, call):
        if self.use_first_suit:
            target_call = None
            for view in history.view_for(self.position).walk:
                target_call = view.last_call
        else:
            target_call = history.view_for(self.position).last_call

        if not target_call or target_call.strain not in suit.SUITS:
            return False
        return call.strain == target_call.strain and history.view_for(self.position).min_length(target_call.strain) >= 3


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
        return history.me.last_call and call.strain == history.me.last_call.strain and call.strain in history.me.bid_suits


class PartnerHasAtLeastLengthInSuit(Precondition):
    def __init__(self, length):
        self.length = length

    @property
    def repr_args(self):
        return [self.length]

    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return history.partner.min_length(call.strain) >= self.length


class MaxShownLength(Precondition):
    def __init__(self, position, max_length, suit=None):
        self.position = position
        self.max_length = max_length
        self.suit = suit


    @property
    def repr_args(self):
        return [self.position.key, self.max_length, self.suit]

    def fits(self, history, call):
        strain = call.strain if self.suit is None else self.suit
        return strain in suit.SUITS and history.view_for(self.position).min_length(strain) <= self.max_length


class DidBidSuit(Precondition):
    def __init__(self, position):
        self.position = position

    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return history.is_bid_suit(call.strain, self.position)


class UnbidSuit(Precondition):
    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return history.is_unbid_suit(call.strain)


class SuitUnbidByOpponents(Precondition):
    def fits(self, history, call):
        if call.strain not in suit.SUITS:
            return False
        return call.strain in history.them.unbid_suits


class UnbidSuitCountRange(Precondition):
    def __init__(self, lower, upper):
        self.lower = lower
        self.upper = upper

    @property
    def repr_args(self):
        return [self.lower, self.upper]

    def fits(self, history, call):
        count = len(history.unbid_suits)
        return count >= self.lower and count <= self.upper


class Strain(Precondition):
    def __init__(self, strain):
        self.strain = strain

    @property
    def repr_args(self):
        return [self.strain]

    def fits(self, history, call):
        return call.strain == self.strain


class Level(Precondition):
    def __init__(self, level):
        self.level = level

    @property
    def repr_args(self):
        return [self.level]

    def fits(self, history, call):
        if call.is_double():
            return history.last_contract.level == self.level
        return call.is_contract() and call.level == self.level


class MaxLevel(Precondition):
    def __init__(self, max_level):
        self.max_level = max_level

    @property
    def repr_args(self):
        return [self.max_level]

    def fits(self, history, call):
        if call.is_double():
            return history.last_contract.level <= self.max_level
        return call.is_contract() and call.level <= self.max_level


class HaveFit(Precondition):
    def fits(self, history, call):
        for strain in suit.SUITS:
            if history.partner.min_length(strain) + history.me.min_length(strain) >= 8:
                return True
        return False


class Jump(Precondition):
    def __init__(self, exact_size=None):
        self.exact_size = exact_size

    @property
    def repr_args(self):
        return [self.exact_size]

    def _jump_size(self, last_call, call):
        if call.strain <= last_call.strain:
            # If the new suit is less than the last bid one, than we need to change more than one level for it to be a jump.
            return call.level - last_call.level - 1
        # Otherwise any bid not at the current level is a jump.
        return call.level - last_call.level

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
