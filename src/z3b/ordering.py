from builtins import range
from builtins import object
import functools
import networkx

class Ordering(object):
    @functools.total_ordering
    class OrderedItem(object):
        def __init__(self, ordering, item):
            self._ordering = ordering
            self._item = item

        def __eq__(self, other):
            return self._item == other._item

        def __lt__(self, other):
            return self._ordering.lt(self._item, other._item)

    def __init__(self):
        self._graph = networkx.DiGraph()
        self._compiled = True

    def lt(self, left, right):
        self._compile()

        return self._graph.has_edge(left, right)

    def key(self, item):
        return Ordering.OrderedItem(self, item)

    def order(self, *args):
        self._compiled = False

        result = set()
        for blob in args:
            for item in self._iterate(blob):
                result.add(item)

        for i in range(len(args)-1):
            for lower in self._iterate(args[i]):
                for higher in self._iterate(args[i+1]):
                    self._graph.add_edge(lower, higher)

        return result

    def _compile(self):
        if self._compiled:
            return

        for left in self._graph.nodes_iter():
            for right in networkx.descendants(self._graph, left):
                self._graph.add_edge(left, right)

        self._check_cycles()
        self._compiled = True

    def _check_cycles(self):
        if not networkx.is_directed_acyclic_graph(self._graph):
            assert False, "Cycle detected"

    def _iterate(self, list_or_not):
        try:
            for item in list_or_not:
                yield item
        except TypeError:
            yield list_or_not
