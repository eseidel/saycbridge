# Python does not (yet) seem to provide automatic memoization.

import functools


class memoized(object):
    """Memoize a method's result on the *instance*.

    Every use in this codebase is a method (accessed through __get__), so the
    cache is stored on the instance under __memoized_cache__ and lives exactly
    as long as the instance does.  The previous version kept a single dict on
    the (class-level, process-lifetime) decorator object keyed by ``self``,
    which pinned every object ever passed as ``self`` -- e.g. every History and
    RuleSelector built while interpreting an auction -- for the life of the
    process.  That was the z3b memory leak (~2-3 MB per web request).
    """

    def __init__(self, function):
        self._function = function
        functools.update_wrapper(self, function)

    def _cache_for(self, instance):
        # One dict per instance, created lazily. Keyed by the decorator object
        # (unique per decorated method) plus the call args.
        try:
            cache = instance.__memoized_cache__
        except AttributeError:
            cache = {}
            instance.__memoized_cache__ = cache
        return cache

    def __call__(self, instance, *args):
        cache = self._cache_for(instance)
        key = (self, args)
        try:
            return cache[key]
        except KeyError:
            # If we didn't find the args in our cache, call and save the results.
            result = self._function(instance, *args)
            cache[key] = result
            return result
        # FIXME: We may need to handle TypeError here in the case
        # that "args" is not a valid dictionary key.

    def take(self, instance, *args):
        cache = self._cache_for(instance)
        result = self.__call__(instance, *args)
        del cache[(self, args)]
        return result

    # Use python "descriptor" protocol __get__ to appear
    # invisible during property access.
    def __get__(self, instance, owner):
        if instance is None:
            return self
        # Return a function partial with obj already bound as self.
        partial = functools.partial(self.__call__, instance)
        partial.take = functools.partial(self.take, instance)
        return partial
