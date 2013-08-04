Bridge Background
----------------

Read [Wikipedia's Bridge Article](https://en.wikipedia.org/wiki/Contract_bridge)

*SAYC Bridge (currently) only deals with the bidding phase of bridge.*

Standard American Yellow Card, or SAYC is one of the various bidding systems
for Contract Bridge.  Our implementation is based on SAYC as defined by:
http://www.amazon.com/Standard-Bidding-With-SAYC-Downey/dp/1897106033



SAYC Bridge Core Data Types
---------------------------

 - Call, has a level: 1234567 and a strain: CDHSN
 - Pass, a subclass of Call with no level or strain
 - Bid, the set of Calls which are not Pass.
 - Call History, a list of calls (and the Vulnerability and who the dealer is)
 - Contract, a call (the last of a Call history) + whether it was doubled/redoubled.

 - Card, value: 123456789TJQKA and a suit: CDHS
 - Hand, list of cards
 - Deal, 4 hands
 - Position, given in cardinal directions: NEWS
 - Board is the global state, Deal + CallHistory + Board Number


Bidding Logic Overview
----------------------

Interpreter
 - Produces some sort of "state of the world" object from a Call History

Bidder
 - Given a Hand, and a CallHistory, produces a Call.


Knowledge Based Bidder
----------------------

Knowledge Based Bidder was our second attempt at writing a bidder for SAYC.
The core insight of the Knowledge Based Bidder is that Bidding should work
"backwards" that bidding is a secondary effect of *interpreting* bids.

The KBB accumulates the state of the world, in a (limited, see below) Knowledge
object, which contains constraints over the hands ( < 10hcp, 4+ spades, etc.)

KBB starts with an *ordered* set of Rule objects (listed in kbb/interpreter.py).

Given a Hand, a CallHistory, the KBB considers all possible Calls over that history.
For each possible call, the KBB walks its list of rules.

For each Rule and possible Call:
 - Each Rule is handed the current accumulated Knowledge (which it can modify).
 - Each rule could optionally "consume" the call under consideration (return None).
 - As soon as one rule "consumes" the bid, the loop terminates.

The ConsistencyOracle then validates that the resulting Knowledge is consistent with the passed in hand.
If the new knowledge is consistent with the hand, the Bid, Rule and Knowledge are saved.

Once all possible calls have been examined, priorities are caculated for these calls,
again by asking the Rule what priority it would assign that call over the given history.

Finally the priorities are compared for all the calls, and the highest priority call is selected.

If multiple bids existed with the same priority, the KBB would select the highest possible bid.


The KBB's Limited Knowledge
---------------------------

One of the factors which prompted the (in-progress) re-write of the SAYC Bridge
bidding engine, is the limited nature of the KBB's Knowledge.

The KBB can only represent "a rectilinear constraints over suit length and points".

The KBB's knowledge can only represent conjunctions (ANDs) of convex ranges over
its various dimensions (points, suits, honor concentration).

The KBB can represent a hand constrained to 5-10 hcp and 5+ hearts, but it cannot
represent OR, e.g. it can't understand "2 Clubs" as 22+hcp OR 9+ quicktricks.

OR-based rules are rather common in SAYC, so based on this limitiation
(and various smaller problems) we decided to start again.


The Z3 Bidder
-------------

The Z3 Bidder (z3b) is our 3rd attempt at writing a bidder for SAYC and uses
Microsoft Research's [Z3 theorem prover](http://z3.codeplex.com/) to describe it's Knowlege model.

Unlike the KBB, the Z3B (due to Z3) is easily capable of representing OR constraints
(e.g. a 1S overcall may be 8+ points AND 5+ spades OR a good 4-card suit.)

Unlike the KBB, the Z3B's Rules are NOT globally ordered.  Global ordering in the
KBB caused confusion where seamingly incomprable Bids would unexpectedly have an ordering.

Instead the KBB uses a PartialOrdering (z3b/orderings.py) any two Rules which
have not be explicitly ordered raise an Exception when compared.

Unlike the KBB, the Z3B does not consider all possible calls over a History.
Instead, the Z3B asks each Rule for all Calls it knows how to make over a given History.


Priorities in the Z3B
---------------------

Before discussing the actual bidding, it's important to understand the Z3B's more
complicated priority system.

The KBB had two priority systems (global ordering of Rules and explicit priorities for Calls).

Z3 Bidder has 3 separate priority systems:

 1. Intra-Bid priorities ("category" in the code).
    "Alert! 2N is 'Unusual' here and not a natural bid."  Allows segregating the
    bidding system w/o needing to teach each rule about the exceptions.

 2. Inter-Bid priorities ("priority" in the code) used for comparing possible bids
    "With 5-5 in the majors, do I open 1H or 1S?"

 3. Tie-Breaking priorities ("needs_planning", mostly unimplemented).
    These apply when you legitimately have multiple possible bids and are
    the only priorities which are computed *with access to the hand*.  These will
    likely be used as part of eventual Slam bidding.


How Z3B selects a Call
----------------------

To make a Call, Z3B:

 1. Collects all the knowledge (for the 4 positions) from the existing CallHistory into a "History" object.

 2. Asks all Rules for possible calls over that history and collects a
    Call -> Highest-Category-Rule mapping in the RuleSelector object.

 3. Creates a Call -> Priority mapping from the Rule selector.

 4. Using the PartialOrdering, compares the possible calls, selecting the maximal_priority calls.

 5. Applies tie-breaking priorities (able to consider the Hand).

And returns the highest priority call from the above.


The Anatomy of a Rule
---------------------

Both the KBB and the Z3B use Rule objects to represent the idea of a Convention
in a bidding system.  Stayman might be an example rule, as is OneNoTrumpOpening.

The KBB and Z3 hold differnet information on their Rule objects, but both have at least:

 - Preconditions -- Given the current Knowledge/History and a Call, can this Rule apply?
 - Constraints -- What affect on the Knowledge would making this Call have?
 - Priority -- (Described in depth above) various information about how Calls should be compared.

For Z3, most of the Constraints are written directly in Z3's nice DSL (Domain Specific Language).

Some of the Constraints are more complicated and implemented in terms of Constraint objects (src/z3b/constraints.py).
