import werkzeug
import werkzeug.serving

import appengine_main
import os.path

gae_dir = os.path.dirname(__file__)

# Alternately we could read app.yaml and setup the static paths from that.
app = werkzeug.SharedDataMiddleware(appengine_main.app, {
    '/scripts': os.path.join(gae_dir, 'scripts'),
    '/stylesheets': os.path.join(gae_dir, 'stylesheets'),
    '/images': os.path.join(gae_dir, 'images'),
    '/static': os.path.join(gae_dir, 'static'),
    '/fight': os.path.join(gae_dir, 'static', 'fight.html')
})
