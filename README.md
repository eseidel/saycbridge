SAYC Bridge
===========

[![Build Status](https://travis-ci.org/eseidel/saycbridge.png?branch=master)](https://travis-ci.org/eseidel/saycbridge)

A Python library and Google App Engine instance for bidding bridge hands
using Standard American Yellow Card conventions.

- http://www.saycbridge.com/
- https://play.google.com/store/apps/details?id=com.saycbridge.bridge
- http://saycbot.appspot.com/


Warning
-------

The SAYC Bridge code is currently undergoing an re-write.

The code at saycbridge.com runs on Google App Engine
and uses the (deprecated) Knolwedge Based Bidder (KBB)
which can be checked out from the "kbb" branch.

All active development is focused on the new z3 bidder (src/z3b)
which is currently only hosted on z3b.saycbridge.com.

The z3b is nearly ready to replace the kbb on www.saycbridge.com.


Development
-----------

The typical development cycle:

    # Make changes to the bidder (src/z3b)
    make check
    # Bah, my changes don't work as expected!
    # Try ./scripts/test-hand and ./scripts/explain to understand why.
    # Use http://localhost:8080/explorer to understand my changes better.
    # Fix my changes to actually work.
    make accept
    git commit


Testing Setup
-------------

We highly recommend you use virtualenv:

    sudo pip install virtualenv
    virtualenv sayc-env
    bash sayc-env/bin/activate

To get and compile all the dependencies:

    git submodule update --init
    make deps


Running SAYCBridge.com Locally
------------------------------

You can run the SAYCBridge web-interface in a local development server using

    make serve # A very experimental version of the site using the z3 Bidder

Running the server will require CoffeeScript:

    sudo npm install -g coffee-script

If you don't already have npm, you can get it from Node.js
http://nodejs.org/


Useful URLs
-----------

 - /unittests -- Shows you an html-colorized view of the current z3b_baseline.txt file
 - /explore -- Lets you walk around in the Bidder's little brain


Where To Start
--------------

One place to start is looking at None results in the unittests:
FAIL: None (expected 2C) for T874.876.86.J843 (hcp: 1 lp: 1 sp: 2), history: 1S X P
These are where the bidder failed to make a call.

Similarly, when you run the site locally, all None bids will
show as "Pass" with an orange background to highlight the error.

Either browsing around the site (make serve), or running the unittests
is a great way to find bids which are wrong or missing rules.

New rules can be added to src/z3b/rules.py


Code Layout
-----------

- dist -- All the code for the various "App" versions of SAYCBridge, incuding iOS,
  Android, Chrome App, and the saycbridge.com Google App Engine instance.
- dist/gae/handlers -- GAE handlers (code to respond to requests at www.saycbridge.com)
- dist/gae/scripts -- CoffeeScript files supporting the web-front-end for the bidder
- dist/gae/templates -- GAE templates (generate the HTML and JSON served at www.saycbridge.com)
- pr -- Images, logos, screenshots, etc needed for submisison to the various App stores
- scripts -- Various scripts used for testing.
- src -- Python back-end for SAYCBridge
- src/core -- Basic Python objects for dealing with bridge hands/boards
- src/third_party -- External code goes here
- src/z3b -- Z3 Bidder (new bidder on top of MSR's Z3 Theorem Prover)


Make Targets
------------

    make check  # check your latest changes against your baseline.txt
    make accept # replace the current baseline file with your last make check results
    make clean  # remove all *.pyc files
    make serve


Testing Scripts
---------------

    scripts/test-hand [EXPECTED_CALL] HAND_STRING [HISTORY_STRING]
    scripts/explain HISTORY_STRING
    scripts/test-sayc # Runs the unit tests.
    scripts/saycbot.py [-a] # Command-line interactive bidder.  -a auto-bids all hands (for finding crashes).


Performance Testing
-------------------

    scripts/test-sayc -p

will run the unittests with the python cProfile module.
It will also print instructions on how to read the profile data.


Wrappers and Mobile Apps
------------------------

There are Chrome OS, iOS, and Android wrappers / apps for SAYC Bridge:

- Development of the Android wrapper requires Eclipse and the [Android SDK](http://developer.android.com/sdk/).
- Development of the iOS wrapper requires Apple's [Xcode](https://developer.apple.com/xcode/).

The code for these can all be found in the "dist" directory.
