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

baseline:
	@$(appengine_dir)/test-sayc > $(appengine_dir)/kbb_baseline.txt ; true

baseline-z3:
	@$(appengine_dir)/test-sayc -z > $(appengine_dir)/z3b_baseline.txt ; true

accept:
	@mv $(appengine_dir)/kbb_actual.txt $(appengine_dir)/kbb_baseline.txt

accept-z3:
	@mv $(appengine_dir)/z3b_actual.txt $(appengine_dir)/z3b_baseline.txt

check: clean
	@$(appengine_dir)/test-sayc > $(appengine_dir)/kbb_actual.txt ; true
	@diff -U 7 $(appengine_dir)/kbb_baseline.txt $(appengine_dir)/kbb_actual.txt ; true

check-z3: clean
	@$(appengine_dir)/test-sayc -z > $(appengine_dir)/z3b_actual.txt ; true
	@diff -U 7 $(appengine_dir)/z3b_baseline.txt $(appengine_dir)/z3b_actual.txt ; true

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

serve: clean
	coffee --watch --compile $(scripts_dir)/*.coffee &
	python2.7 `which dev_appserver.py` $(appengine_dir) --use_sqlite

publish: compile
	@appcfg.py --oauth2 --email=macdome@gmail.com update $(appengine_dir)

chromeapp:
	zip -r bridge.zip dist/crx/*
