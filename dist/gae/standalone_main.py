import werkzeug.serving
import standalone_app

werkzeug.serving.run_simple('10.1.10.114', 8080, standalone_app.app, use_reloader=True)
