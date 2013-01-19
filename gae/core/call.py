from suit import *


class Call(object):
    def __init__(self, name):
        self.name = name
        self.strain = None if self.name in ('P', 'X', 'XX') else strain_from_char(self.name[1])
        self._validate()

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Call('%s')" % self.name

    def _validate(self):
        if self.is_contract():
            assert len(self.name) == 2, "%s is not a valid call name" % self.name
            assert self.level() in range(8) and self.strain in STRAINS
        else:
            assert self.name in ('P', 'X', 'XX'), "%s is not a valid call name" % self.name

    # It's unclear how forgiving we should be with this method.
    # We may want to split this into different methods for different
    # input sources.
    @classmethod
    def from_string(self, string):
        string = string.upper()
        string = string.replace("NT", "N")
        string = string.replace("PASS", "P")
        string = string.replace("DOUBLE", "X")
        if len(string) != 2 and string not in ("P", "X"):
            return None
        return Call(string)

    # This is an odd way of saying "not pass, not double, not redouble"
    def is_contract(self):
        return self.strain is not None

    def is_pass(self):
        return self.name == "P"

    def level(self):
        if not self.is_contract():
            return None
        return int(self.name[0])

    def suit(self):
        if not self.is_contract():
            return None
        return strain_from_char(self.name[1])

    def is_double(self):
        # FIXME: It's unclear if double should include the information about the
        # bid it's doubling or not.  (i.e. 1NX)
        return self.name == "X"

    def is_redouble(self):
        return self.name == "XX"

    def __cmp__(self, other):
        if other is None:
            # We should never need this, but this sorts Call() objects after None.
            # FIXME: 'None not in calls' seems to require call.__cmp__(None), perhaps this is a Python 2.5 bug?
            return 1
        # This will order all non-contracts before contract bids.
        # So we'll end up with 'P', 'X', 'XX', '1C', ... '7N'.
        if self.is_contract() != other.is_contract():
            if other.is_contract():
                return -1
            return 1
        if not self.is_contract():
            # This should return 'P', 'X', 'XX' which seems reasonable.
            return cmp(self.name, other.name)
        # Level comparisons are more important than suit comparisons, so 1S will be before 2C.
        if self.level() != other.level():
            return cmp(self.level(), other.level())
        # Using the suit enum, this comparison is very easy and will correctly order C, D, H, S
        return cmp(self.strain, other.strain)


# This is a convenience for an old method of specifying calls.
class Pass(Call):
    def __init__(self):
        Call.__init__(self, 'P')
