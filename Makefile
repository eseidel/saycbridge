.PHONY: all clean baseline accept check compile serve publish chromeapp

src_dir = src
scripts_dir = scripts

appengine_dir = dist/gae
appengine_scripts_dir = $(appengine_dir)/scripts


PYTHON_PACKAGES=networkx unittest2 werkzeug webapp2 webob jinja2
# Prod packages: cherrypy

PYTHON_EGGS=$(patsubst %,sayc-env/%.STAMP,$(PYTHON_PACKAGES))

all:
	@echo "Run 'make check' to check against the current baseline and 'make accept' to set a new baseline from the last results."

sayc-env:
	@virtualenv sayc-env

sayc-env/%.STAMP: sayc-env
	# source doesn't seem to play nice with /bin/sh
	@. sayc-env/bin/activate && easy_install $(patsubst sayc-env/%.STAMP,%,$@) && touch $@

env: $(PYTHON_EGGS)
ifndef VIRTUAL_ENV
	@echo "Type 'source sayc-env/bin/activate' to activate the virtual environment."
endif

clean:
	@find . -name "*.pyc" -print0 | xargs -0 rm

accept:
	@mv $(src_dir)/z3b_actual.txt $(src_dir)/z3b_baseline.txt

check: clean env
	@$(scripts_dir)/test-sayc -f > $(src_dir)/z3b_actual.txt && diff -U 7 $(src_dir)/z3b_baseline.txt $(src_dir)/z3b_actual.txt ; true

serve: clean
	# Source map generation uses passed-in paths.
	cd $(appengine_dir); coffee --watch --map --compile scripts/*.coffee &
	# FIXME: Doesn't python just have a -C to change CWD before executing?
	cd $(appengine_dir); python2.7 standalone_main.py

serve-prod: clean compile
	@. sayc-env/bin/activate && cd $(appengine_dir) && python2.7 production_main.py

compile:
	coffee --compile $(appengine_scripts_dir)/*.coffee

deploy:
	git push origin origin/master:production
	ssh serve@z3b.saycbridge.com 'killall python2.7 -INT'

# FIXME: Need some way to make this work from a macro instead of an explicit list of files.
closure:
	java -jar compiler.jar \
		--js=$(appengine_scripts_dir)/third_party/jquery-1.6.2.min.js \
		--js=$(appengine_scripts_dir)/third_party/jquery.history.js \
		--js=$(appengine_scripts_dir)/third_party/bignumber.js \
		--js=$(appengine_scripts_dir)/model.js \
		--js=$(appengine_scripts_dir)/controller.js \
		--js=$(appengine_scripts_dir)/view.js \
		--js=$(appengine_scripts_dir)/play.js \
		--js_output_file=bidder.js

chromeapp:
	zip -r bridge.zip dist/crx/*
