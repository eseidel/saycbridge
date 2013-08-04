# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

from third_party import enum

# These priorities are listed from highest priority bid, to lowest priority bid.
priorities = enum.Enum(
    "Stayman",

    "SuperAcceptResponseToJacobyTransfer",
    "ResponseToJacobyTransfer",

    "MinorGameForceRebidAfterStayman",

    "LongMajorSlamInvitiation",
    "JacobyTransferToBetterMajor",
    "JacobyTransfer",
    "QuantitativeFourNotrump",
    "QuantitativeFiveNotrump",

    "Jacoby2N",  # More important than NotrumpGame, if we might have a trump-slam, we want to find it!
    "NotrumpJumpRebid",
    "JumpShift",
    "GameJumpRaiseResponseToMajorOpen",
    "JumpRaiseResponseToMajorOpenAfterRHOTakeoutDouble",
    "JumpRaiseResponseToMinorOpenAfterRHOTakeoutDouble",
    "RaiseResponseToMajorOpen", # Always best to raise partner's major if possible.

    # Responses to 2C:
    "GoodSuitOppositeTwoClubOpen",
    "NoBidableSuitOppositeTwoClubOpen",
    "NegativeResponseOppositeTwoClubs",

    "StrongTwoClubs",

    "TakeoutDouble",  # We would rather takeout double, than bid a 1N overcall if possible, even if we have Ax in their suit.

    "NotrumpOpen",
    "NotrumpOvercall",

    "FeatureResponseToTwoNotrumpFeatureRequest",
    "NotrumpResponseToTwoNotrumpFeatureRequest",

    # FIXME: Another way to order opening bids might be:
    # FiveCardOpen, FourCardOpen, ThreeCardOpen

    # 1-level openings in a non-reverse world:
    "LongestMajor",
    "HigherMajor",
    "LowerMajor",
    "LongestMinor",
    "LowerMinor",
    "HigherMinor",

    "NegativeDouble",  # FIXME: New 5-card suits are higher priority than NegativeDouble.

    # This bid is more bidding-space efficient than the other ways of representing these holding.
    "CueBidAfterNegativedDouble",
    "CueBidAfterTakeoutDouble",
    "CuebidResponseToDirecOvercall",  # FIXME: Cuebids to show minior support be lower pririty than NewSuit of a Major.

    "LongestNewMajor",
    "LowerFourCardMajor",
    "HigherFourCardMajor",

    "NotrumpJumpOverMinor",  # NT Jump is better than mentioning a second minor.

    "NewSuit", # Mentioning a new suit suit at the one level is a higher priority than a 2-level reverse.
    "Reverse",

    # Showing two long suits is almost always better than showing one.
    "UnusualNotrump",
    "MichaelsCuebid",

    # Preempts are lower priority than openings, but higher priority than overcalls.
    "FourLevelPreempt",
    "ThreeLevelPreempt",
    "TwoLevelPreempt",

    "DirectOvercall",
    "BalancingJumpOvercall",
    "BalancingSuitedOvercall",

    "OpenerRebidAfterLimitRaise",

    "NotrumpSlam",

    "TwoNotrumpFeatureRequest",

    "DelayedSupportByOpener",  # More important to show delayed support than directly bid game.

    "MajorGame",
    "NotrumpGame",
    "MinorGame",

    "RaiseResponseToMinorOpen",  # Raising a minor is a very low priority.

    "Default",

    "SettleForGame",
    "SettleForSuitedPartScore",
    # FIXME: We probably want separate ToPlay priorities for partscores vs. game and above.
    # Suits are better for part scores, NT is better for slam (if you have the points and stoppers).
    "SuitedToPlay",
    "SettleForNotrumpPartScore",
    "NotrumpToPlay",

    "LawOfTotalTricks",
    "MichaelsMinorRequest", # FIXME: Unclear when we should plan this, but it should be a relatively low priority.
    "NotrumpWithoutStoppers",

    "EscapeToSuitedContract", # Last ditch, we have nothing better to do, but are forced to bid.

    "Pass",
    "InvalidBid",
)
