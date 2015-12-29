.PHONY: all deps clean check accept compile serve deploy

src_dir = src
scripts_dir = scripts

appengine_dir = dist/gae
appengine_scripts_dir = $(appengine_dir)/scripts

z3_dir = third_party/z3
PYTHON_PACKAGES=networkx unittest2 werkzeug webapp2 webob jinja2

all:
	@echo "Run 'make deps' to bring your dependencies up-to-date."
	@echo "Run 'make check' to check against the current baseline and 'make accept' to set a new baseline from the last results."

deps: z3
	@pip install $(PYTHON_PACKAGES)

z3:
	@cd $(z3_dir) && python scripts/mk_make.py --prefix=$(shell python2.7 -c "import sys; print sys.prefix")
	@make -C $(z3_dir)/build all install

clean:
	@find . -name "*.pyc" | perl -nle unlink

accept:
	@mv $(src_dir)/z3b_actual.txt $(src_dir)/z3b_baseline.txt

check: clean
	@$(scripts_dir)/test-sayc -f > $(src_dir)/z3b_actual.txt && diff -U 7 $(src_dir)/z3b_baseline.txt $(src_dir)/z3b_actual.txt

serve: clean
	# Source map generation uses passed-in paths.
	@cd $(appengine_dir) && coffee --watch --map --compile scripts/*.coffee &
	# FIXME: Doesn't python just have a -C to change CWD before executing?
	@cd $(appengine_dir) && python2.7 standalone_main.py

serve-prod: clean compile
	@cd $(appengine_dir) && python2.7 production_main.py

compile:
	coffee --compile $(appengine_scripts_dir)/*.coffee

deploy:
	git push deploy master

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
