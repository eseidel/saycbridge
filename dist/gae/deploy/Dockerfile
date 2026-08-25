# saycbridge on Python 3. Build context is a checkout of the repository.
# z3 comes from the z3-solver wheel (no vendored submodule).
# Layer order: apt + pip deps (rarely change) before the app COPY so app-only
# pushes rebuild in seconds.
FROM docker.io/library/python:3.12-slim-bookworm

# coffee-script compiles the front-end; git for BIDDER_REVISION at import time;
# uWSGI needs a C toolchain to build.
RUN apt-get update \
 && apt-get install -y --no-install-recommends nodejs npm git gcc libc6-dev \
 && npm install -g coffee-script@1.12.7 \
 && rm -rf /var/lib/apt/lists/*

# Deps per requirements.txt / src/pyproject.toml (webapp2 -> webapp3,
# z3 -> z3-solver wheel). Pinned loosely to what runs today; bump deliberately.
RUN pip install --no-cache-dir \
    "networkx>=2.8.3,<4" "werkzeug>=3,<4" webapp3 "jinja2>=3,<4" ijson webob \
    "z3-solver>=4.8.17" "uwsgi>=2.0.23,<2.1" \
 && apt-get purge -y gcc libc6-dev && apt-get autoremove -y

COPY . /app
RUN cd /app/dist/gae/public && coffee --compile static/scripts/*.coffee

WORKDIR /app/dist/gae
# --master respawns recycled/dead workers. The bidder leaks ~2-3 MB/request, so
# --reload-on-rss recycles a worker once its RSS exceeds 200 MB (base ~70 MB);
# --max-requests is a coarse backstop. 2 workers is plenty for this traffic and
# keeps peak memory well under the container cap in saycbridge.container.
CMD ["uwsgi", "--master", "--http-socket", "/sockets/saycbridge.sock", "--chmod-socket=666", \
     "--processes", "2", "--max-requests", "500", "--reload-on-rss", "200", \
     "--worker-reload-mercy", "10", "--wsgi-file", "app.py"]
