SAYC Bridge
===========

A Python library and Google App Engine instance for bidding bridge hands
using Standard American Yellow Card conventions.

- http://www.saycbridge.com/
- https://play.google.com/store/apps/details?id=com.saycbridge.bridge
- http://saycbot.appspot.com/

Development
-----------

The typical development cycle:

    # Make changes to the bidder (src/z3b)
    make check
    # Validate that your changes are good.
    make accept
    git commit

You can also test the site (saycbridge.com) locally using:

    make serve-kbb # WARNING: This uses the Knowledge Based Bidder, not the z3 bidder.

Setup
-----

Before the above will work, you probably need:
Google App Engine SDK:
https://developers.google.com/appengine/

Running the unittests requires unittest2:

    sudo easy_install unittest2

You will also need a copy of MSR's z3:

- http://z3.codeplex.com/

I recommend cloning their git repository and building directly from there,
however you can also use one of their pre-built binaries.
Their repository requires Git version 1.7 or greater.

I recommend installing z3py directly, but you can also just set PYTHON_PATH in your environment.
Follow their README for instructions on how to build & install z3.

Warning
-------

The SAYC Bridge code is currently undergoing an re-write.

The code at saycbridge.com runs on Google App Engine
and uses the Knolwedge Based Bidder (src/kbb).

However, the Knowledge Based Bidder is deprecated, and
development is continuing on the new z3 bidder (src/z3b).

The z3 bidder is also not nearly complete enough to replace
the Knowledge Based Bidder, but is rapily improving.

z3 is also not python code, and thus not possible
to deploy to saycbridge.com with our current hosting strategy.
Once we have the z3 bidder working well enough, we'll come
up with an alternate hosting strategy.

Make Targets
------------

    make check  # check your latest changes against your baseline.txt
    make accept # replace the current baseline file with your last make check results
    make clean  # remove all *.pyc files
    make serve-kbb # run a local copy of saycbridge.com for testing

Testing Scripts
---------------

    ./test-hand HAND_STRING [HISTORY_STRING] #  Bids a single hand.
    ./test-sayc # Runs the unit tests.
    ./saycbot.py [-a] # Command-line interactive bidder.  -a auto-bids all hands (for finding crashes).

Performance Testing
-------------------

    ./test-sayc -p

will run the unittests with the python cProfile module.
It will also print instructions on how to read the profile data.

Code Layout
-----------

- dist -- All the code for the various "App" versions of SAYCBridge, incuding iOS, Android, Chrome App, and
  the Google App Engine server
- dist/gae/handlers -- GAE handlers (code to respond to requests at www.saycbridge.com)
- dist/gae/models -- GAE models (storage class for GAE)
- dist/gae/scripts -- CoffeeScript files supporting the web-front-end for the bidder
- dist/gae/templates -- GAE templates (generate the HTML and JSON served at www.saycbridge.com)
- pr -- Images, logos, screenshots, etc needed for submisison to the various App stores
- src -- Python back-end for SAYCBridge
- src/core -- Basic Python objects for dealing with bridge hands/boards
- src/kbb -- Knowledge Based Bidder (deprecated, but "stable" bidder)
- src/third_party -- External code goes here
- src/z3b -- Z3 Bidder (new bidder on top of MSR's Z3 Theorem Prover)

Wrappers and Mobile Apps
------------------------

There are Chrome OS, iOS, and Android wrappers / apps for SAYC Bridge:

- Development of the Android wrapper requires Eclipse and the [Android SDK](http://developer.android.com/sdk/).
- Development of the iOS wrapper requires Apple's [Xcode](https://developer.apple.com/xcode/).

The code for these can all be found in the "dist" directory.


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

The Z3 Bidder (z3b) is our 3rd attempt at writing a bidder for SAYC.

Z3B uses Microsoft Research's [Z3 theorem prover](http://z3.codeplex.com/).

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

The KBB had two priority systems (the global ordering of Rules, as well as priorities for Bids).

Z3 Bidder has 3 separate priority systems:

 1. Intra-Bid priorities ("catagory" in the code).
    "Alert! 2N is 'Unusual' here and not a natural bid."  Allows segregating the
    bidding system w/o needing to teach each rule about the exceptions.

 2. Inter-Bid priorities ("priority" in the code) used for comparing possible bids
    "With 5-5 in the majors, do I open 1H or 1S?"

 3. Tie-Breaking priorities ("needs_planning", mostly unimplemented).
    These apply when you legitimently have multiple possible bids and are
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
