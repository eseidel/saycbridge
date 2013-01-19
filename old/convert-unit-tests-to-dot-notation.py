import re

fd = open("core/sayc_unittest.py", "rw")

lines = fd.read().splitlines()
for line in lines:
    match = re.match(r'^( *\[")([^ "]*) ([^ "]*) ([^ "]*) ([^ "]*)(".*)$', line)
    if match:
        print "%s%s.%s.%s.%s%s" % (
            match.group(1),
            match.group(5),
            match.group(4),
            match.group(3),
            match.group(2),
            match.group(6),
        )
    else:
        print line

fd.close()
