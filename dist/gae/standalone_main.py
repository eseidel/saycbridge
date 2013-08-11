import werkzeug.serving
import standalone_app

werkzeug.serving.run_simple('localhost', 8080, standalone_app.app, use_reloader=True)
