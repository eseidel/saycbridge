# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import json
import networkx.readwrite.json_graph
import webapp2
from z3b.rules import Rule
from z3b.sayc import StandardAmericanYellowCard


class JSONPrioritiesHandler(webapp2.RequestHandler):
    def get(self):
        graph = StandardAmericanYellowCard.priority_ordering.ordering._graph
        link_data = networkx.readwrite.json_graph.node_link_data(graph)

        # Many priority objects aren't json serializable so just repr everything for now.
        for node in link_data['nodes']:
            node['id'] = repr(node['id'])

        self.response.headers["Content-Type"] = "application/json"
        self.response.out.write(json.dumps(link_data))
