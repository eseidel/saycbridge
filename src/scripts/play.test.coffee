
# TODO:
# re-write playHistory.identifier() to be more user editable.
# Need to get rank-promoted values?
# Need to count top-tricks.

# One method might be to compute the appoximate probability of any card in your hand winning a trick
# then select suits with the most unsure winners and play those first?

# v1:
# never takes a finesse
# just plays honor from the short side
# and second hand low.

playTests = [
    ["JT2", "K76", "J"], # p5
    ["AKQ2", "543", "A"], # p8
    ["AK32", "654", "2"], # p9
]

# Opening Lead Suit Selection rules:
# LeadDirectingDouble()
# PartnerSuit()
# LongestAndStrongest()

# Later Lead Suit Selection:
# ThroughStrength()
# RHODummyWeakestSuit()


# Card selection rules:
# FourthDown()
# TopOfDoubleton()
# TopOfNothingAgainstNotrump()
# TopOfHonorSequence()
# Singleton()


# Play rules:
# SecondHandLow()
# ThirdHandHigh()
# FourthHandWin()
# LowestCard()

# DeclarerPlayRules()
# HonorFromTheShortSide()
# 


# NT Declarer play goals:
# Be able to play out a NT hand, taking as many winners as possible w/o losing control.
# Be able to count top tricks and play them.
# Play each suit independantly.
# Honor from the short side (unblocking).


# Later we can consider:
# Never try to develop suits you're shorter than opponents in.
# Will need some way to compare probabilities of distributions?
# Need to be able to count long tricks (i.e when we have 10 bad spades, that's still likely longest - 2 winners, and certainly longest - 3)


# In a trump contract, your first goal is to play the trump (if you can afford it).

