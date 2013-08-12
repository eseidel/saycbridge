import functools

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
        self._items = set()
        self._mapping = {}
        self._compiled = True

    def lt(self, left, right):
        self._compile()

        return bool(self._mapping.get((left, right))

    def cmp(self, left, right):
        self._compile()

        if self._mapping.get((left, right)):
            return -1
        elif self._mapping.get((right, left)):
            return 1
        else:
            return 0

    def key(self, item):
        return Ordering.OrderedItem(self, item)

    def order(self, *args):
        self._compiled = False
        for i in range(len(args)-1):
            self._order(args[i], args[i+1])

        result = set()
        for blob in args:
            for item in self._iterate(blob):
                result.add(item)
        return result

    def _compile(self):
        if self._compiled:
            return

        for middle in self._items:
            for lower in self._items:
                for higher in self._items:
                    if self._mapping.get((lower, middle)) and self._mapping.get((middle, higher)):
                        self._mapping[(lower, higher)] = True

        self._check_cycles()
        self._compiled = True

    def _check_cycles(self):
        for item in self._items:
            assert not self._mapping.get((item, item)), "Cycle detected for item %s" % repr(item)

    def _iterate(self, list_or_not):
        try:
            for item in list_or_not:
                yield item
        except TypeError:
            yield list_or_not

    def _order(self, lower_list, higher_list):
        for lower in self._iterate(lower_list):
            self._items.add(lower)
        for higher in self._iterate(higher_list):
            self._items.add(higher)

        for lower in self._iterate(lower_list):
            for higher in self._iterate(higher_list):
                self._mapping[(lower, higher)] = True
