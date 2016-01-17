.PHONY: run_prod run_dev run_dev_gae clean

PORT ?= 9000
SOCK ?= :$(PORT)
run_dev:
	@uwsgi --http $(SOCK) --master --threads 64 --wsgi-file app.py

run_prod:
	@uwsgi --http-socket $(SOCK) --threads 64 --wsgi-file app.py

run_dev_gae:
	@dev_appserver.py --port $(PORT) app.yaml

clean:
	@find . -name "*.pyc" | perl -nle unlink
