SAYC Bridge
===========

A Python library and Google App Engine instance for bidding bridge hands
using Standard American Yellow Card conventions.

- http://www.saycbridge.com/
- https://play.google.com/store/apps/details?id=com.saycbridge.bridge
- http://saycbot.appspot.com/


Warning
-------

The SAYC Bridge code is currently undergoing an re-write.

The code at saycbridge.com runs on Google App Engine
and uses the (deprecated) Knolwedge Based Bidder (src/kbb).

However, all active development is focused on the new z3 bidder (src/z3b).

The z3 bidder is also not nearly complete enough to replace
the Knowledge Based Bidder, but is rapily improving.


Development
-----------

The typical development cycle:

    # Make changes to the bidder (src/z3b)
    make check
    # Validate that your changes are good.
    make accept
    git commit


Testing Setup
-------------

Running the unittests requires unittest2:

    sudo easy_install unittest2

You will also need a copy of MSR's z3:
http://z3.codeplex.com/

I recommend cloning their git repository and building directly from there.
Their repository requires Git version 1.7 or greater.

Follow their README for instructions on how to build & install z3.


Running SAYCBridge.com Locally
------------------------------

You can run the SAYCBridge web-interface in a local development server using

    make serve # A very experimental version of the site using the z3 Bidder
or
    make serve-kbb # The stable Knowledge Based Bidder

Both versions of the site depend on CoffeeScript:

    sudo npm install -g coffee-script

If you don't already have npm, you can get it from Node.js
http://nodejs.org/

The Z3 Bidder (make serve) site additionally depends on:

    sudo easy_install webapp2 webob jinja2 Werkzeug

The Knowledge Based Bidder version depends on Google App Engine:
https://developers.google.com/appengine/


Useful URLs
-----------

 - /unittests -- Shows you an html-colorized view of the current z3b_baseline.txt file
 - /explore -- Lets you walk around in the Bidder's little brain (not very functional for the Z3B yet)


Where To Start
--------------

The Z3 Bidder does not know how to make many Calls.
When it doesn't know what to bid, it returns None (an error).
An example None from the Unittests:
FAIL: None (expected 2C) for T874.876.86.J843 (hcp: 1 lp: 1 sp: 2), history: 1S X P

Similarly, when you run the site locally, all None bids will
show as "Pass" with an orange background to highlight the error.

Either browsing around the site (make serve), or running the unittests
is a great way to find bids which are wrong or missing rules.

New rules can be added to src/z3b/rules.py

The KBB's (much more complete) rules can be found at src/z3b/rules/
and are often helpful examples of rules to add to the Z3 Bidder.


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
- src/kbb -- Knowledge Based Bidder (deprecated, but "stable" bidder)
- src/third_party -- External code goes here
- src/z3b -- Z3 Bidder (new bidder on top of MSR's Z3 Theorem Prover)


Make Targets
------------

    make check  # check your latest changes against your baseline.txt
    make accept # replace the current baseline file with your last make check results
    make clean  # remove all *.pyc files
    make serve-kbb # run a local copy of saycbridge.com for testing


Testing Scripts
---------------

    scripts/test-hand HAND_STRING [HISTORY_STRING] #  Bids a single hand.
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
