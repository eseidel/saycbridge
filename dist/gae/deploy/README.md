Containerized deployment
========================

Reference files for running the `gae` frontend on Python 3 as a rootless
podman container. They are not consumed by anything in the repo; copy them to
wherever you deploy.

- `Dockerfile` builds the image from a checkout of the repository: installs
  the Python dependencies and coffee-script, compiles the front-end, and runs
  the app under uWSGI on a unix socket at `/sockets/saycbridge.sock`.
- `saycbridge.container` is a systemd quadlet unit for that image: bind-mount
  a host directory onto `/sockets`, no network, read-only rootfs, and a memory
  cap that recycles the container if the bidder's per-request memory growth
  ever gets ahead of uWSGI's own worker recycling (`--reload-on-rss` in the
  Dockerfile).

Put a reverse proxy (nginx or similar) in front of the socket, e.g.
`proxy_pass http://unix:/path/to/saycbridge.sock;`. To ship a new version,
pull the checkout, `podman build -f Dockerfile -t saycbridge .`, and restart the
unit.
