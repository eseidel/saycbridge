from cherrypy import wsgiserver
import standalone_app

server = wsgiserver.CherryPyWSGIServer(
        ('localhost', 8080),
        standalone_app.app,
        numthreads=1 # z3 does not play nice with threads.
    )
try:
    print "Starting..."
    server.start()
except KeyboardInterrupt:
    print
    print "Stopping..."
    server.stop()
