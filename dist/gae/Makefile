.PHONY: run_prod run_dev run_dev_gae clean compile_dev compile

PORT ?= 9000
SOCK ?= :$(PORT)
run_dev: compile_dev
	@uwsgi --http $(SOCK) --master --processes 4 --wsgi-file app.py

run_prod:
	@uwsgi --http-socket $(SOCK) --processes 4 --wsgi-file app.py

run_dev_gae: compile_dev
	@dev_appserver.py --port $(PORT) app.yaml

clean:
	@find . -name "*.pyc" | perl -nle unlink

compile_dev:
	@cd public && coffee --watch --map --compile static/scripts/*.coffee &

compile:
	@cd public && coffee --compile static/scripts/*.coffee
