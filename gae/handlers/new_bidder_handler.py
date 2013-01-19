import webapp2
import jinja2
import os

jinja_environment = jinja2.Environment(loader=jinja2.FileSystemLoader("templates"))


class NewBidderHandler(webapp2.RequestHandler):
    def get(self):
        self.response.out.write(jinja_environment.get_template('new_bidder.html').render())
