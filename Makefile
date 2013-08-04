.PHONY: all clean baseline baseline-z3 accept accept-z3 check check-z3 compile serve publish chromeapp

appengine_dir = gae
scripts_dir = $(appengine_dir)/scripts

THIRD_PARTY_SCRIPTS = \
	third_party/jquery-1.6.2.min.js \
	third_party/jquery.history.js \
	third_party/bignumber.js \

SCRIPTS = \
	model.js \
	controller.js \
	view.js \
	controller.js \
	controller.test.js \
	new_bidder.js \
	play.js \
	play.test.js \
	recap.js \

all:
	@echo "Run 'make baseline' to create baselines and 'make check' to diff the current results."

clean:
	@find . -name "*.pyc" | xargs rm

accept:
	@mv $(appengine_dir)/z3b_actual.txt $(appengine_dir)/z3b_baseline.txt

check: clean
	@$(appengine_dir)/test-sayc -z > $(appengine_dir)/z3b_actual.txt ; true
	@diff -U 7 $(appengine_dir)/z3b_baseline.txt $(appengine_dir)/z3b_actual.txt ; true


# Support for the old Knowledge Based Bidder:

accept-kbb:
	@mv $(appengine_dir)/kbb_actual.txt $(appengine_dir)/kbb_baseline.txt

check-kbb: clean
	@$(appengine_dir)/test-sayc > $(appengine_dir)/kbb_actual.txt ; true
	@diff -U 7 $(appengine_dir)/kbb_baseline.txt $(appengine_dir)/kbb_actual.txt ; true


compile:
	coffee --compile $(scripts_dir)/*.coffee

# $(scripts_dir)/%.js: $(scripts_dir)/%.coffee
# 	coffee --compile $<

# FIXME: Need some way to make this work from a macro instead of an explicit list of files.
closure:
	java -jar compiler.jar \
		--js=$(scripts_dir)/third_party/jquery-1.6.2.min.js \
		--js=$(scripts_dir)/third_party/jquery.history.js \
		--js=$(scripts_dir)/third_party/bignumber.js \
		--js=$(scripts_dir)/model.js \
		--js=$(scripts_dir)/controller.js \
		--js=$(scripts_dir)/view.js \
		--js=$(scripts_dir)/play.js \
		--js_output_file=bidder.js

# FIXME: Currently there is no way to run the site with the z3 bidder.
# AppEngine runs in a hermetic python environment which is incapable
# of running z3.
serve-kbb: clean
	coffee --watch --compile $(scripts_dir)/*.coffee &
	python2.7 `which dev_appserver.py` $(appengine_dir)

publish: compile
	@appcfg.py --oauth2 --email=macdome@gmail.com update $(appengine_dir)

chromeapp:
	zip -r bridge.zip dist/crx/*
