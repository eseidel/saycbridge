SAYC Bridge
===========

A Python library and Google App Engine instance for bidding bridge hands
using Standard American Yellow Card conventions.

- [http://www.saycbridge.com/](http://www.saycbridge.com/)
- [https://play.google.com/store/apps/details?id=com.saycbridge.bridge](https://play.google.com/store/apps/details?id=com.saycbridge.bridge)
- [http://saycbot.appspot.com/](http://saycbot.appspot.com/)

Development
-----------

The typical development cycle:

    # Make changes to the bidder (gae/z3b)
    make check
    # Validate that your changes are good.
    make accept
    git commit

You can also test the site (saycbridge.com) locally using:
make serve

Setup
-----

Before the above will work, you probably need:
Google App Engine SDK:
https://developers.google.com/appengine/

Running the unittests requires unittest2:

    sudo easy_install unittest2

You will also need a copy of MSR's z3:
http://z3.codeplex.com/

I recommend cloning their git repository and building directly from there,
however you can also use one of their pre-built binaries.
Their repository requires Git version 1.7 or greater.

I recommend installing z3py directly, but you can also just set PYTHON_PATH in your environment.
Follow their README for instructions on how to build & install z3.

Warning
-------

The SAYC Bridge code is currently undergoing an re-write.

The code at saycbridge.com runs on Google App Engine
and uses the Knolwedge Based Bidder (gae/kbb).

However, the Knowledge Based Bidder is deprecated, and
development is continuing on the new z3 bidder (gae/z3b).

The z3 bidder is also not nearly complete enough to replace
the Knowledge Based Bidder, but is rapily improving.

z3 is also not python code, and thus not possible
to deploy to saycbridge.com with our current hosting strategy.
Once we have the z3 bidder working well enough, we'll come
up with an alternate hosting strategy.

Make Targets
------------

    make serve  # run a local copy of saycbridge.com for testing
    make check  # check your latest changes against your baseline.txt
    make accept # replace the current baseline file with your last make check results
    make clean  # remove all *.pyc files

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

- dist -- All the code for the various "App" versions of SAYCBridge, incuding iOS, Android and Chrome App
- gae -- The Google App Engine (GAE) Python back-end for SAYCBridge
- pr -- Images, logos, screenshots, etc needed for submisison to the various App stores
- gae/core -- Basic Python objects for dealing with bridge hands/boards
- gae/handlers -- GAE handlers (code to respond to requests at www.saycbridge.com)
- gae/kbb -- Knowledge Based Bidder (deprecated, but "stable" bidder)
- gae/models -- GAE models (storage class for GAE)
- gae/scripts -- CoffeeScript files supporting the web-front-end for the bidder
- gae/templates -- GAE templates (generate the HTML and JSON served at www.saycbridge.com)
- gae/third_party -- External code goes here
- gae/z3b -- Z3 Bidder (new bidder on top of MSR's Z3 Theorem Prover)

Wrappers and Mobile Apps
------------------------

There are Chrome OS, iOS, and Android wrappers / apps for SAYC Bridge:

Development of the Android wrapper requires Eclipse and the [Android SDK](http://developer.android.com/sdk/).

Development of the iOS wrapper requires Apple's [Xcode](https://developer.apple.com/xcode/).

The code for these can all be found in the "dist" directory.
