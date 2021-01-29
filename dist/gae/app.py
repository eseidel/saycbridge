import main
import os
import werkzeug

public_root = os.path.join(os.path.dirname(__file__), 'public')
application_with_static = werkzeug.wsgi.SharedDataMiddleware(main.application, {
  '/favicon.ico': os.path.join(public_root, 'favicon.ico'),
  '/robots.txt':  os.path.join(public_root, 'robots.txt'),
  '/apple-touch-icon-57x57.png': os.path.join(public_root, 'apple-touch-icon-57x57.png'),
  '/apple-touch-icon-72x72.png': os.path.join(public_root, 'apple-touch-icon-72x72.png'),
  '/apple-touch-icon-114x114.png': os.path.join(public_root, 'apple-touch-icon-114x114.png'),
  '/static':      os.path.join(public_root, 'static'),
})

def application(environ, start_response):
  if not environ.get('SCRIPT_NAME'):
    script_name = environ.get('HTTP_X_SCRIPT_NAME', '')
    path_info = environ.get('PATH_INFO', '')
    if not (path_info == script_name or path_info.startswith(script_name + '/')):
      raise RuntimeError("The script name is not a prefix of the path!")

    environ['SCRIPT_NAME'] = script_name
    environ['PATH_INFO'] = path_info[len(script_name):]

  return application_with_static(environ, start_response)
