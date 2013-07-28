# Python does not (yet) seem to provide automatic memoization.

import functools


class memoized(object):
    def __init__(self, function):
        self._function = function
        self._results_cache = {}

    def __call__(self, *args):
        try:
            return self._results_cache[args]
        except KeyError:
            # If we didn't find the args in our cache, call and save the results.
            result = self._function(*args)
            self._results_cache[args] = result
            return result
        # FIXME: We may need to handle TypeError here in the case
        # that "args" is not a valid dictionary key.

    def take(self, *args):
        result = self(*args)
        del self._results_cache[args]
        return result

    # Use python "descriptor" protocol __get__ to appear
    # invisible during property access.
    def __get__(self, instance, owner):
        # Return a function partial with obj already bound as self.
        partial = functools.partial(self.__call__, instance)
        partial.take = functools.partial(self.take, instance)
        return partial
