
from z3b.rules import *
from z3b.cappelletti import *


def _get_subclasses(base_class):
    subclasses = base_class.__subclasses__()
    for subclass in list(subclasses):
        subclasses.extend(_get_subclasses(subclass))
    return subclasses

def _concrete_rule_classes():
    return filter(lambda cls: not cls.__subclasses__(), _get_subclasses(Rule))


class StandardAmericanYellowCard(object):
    # Rule ordering does not matter.  We could have python crawl the files to generate this list instead.
    # rules cannot currently be a set() as CompiledRule is not hashable.
    rules = [RuleCompiler.compile(description_class) for description_class in _concrete_rule_classes()]
    assert len(rules) == len([rule.name for rule in rules]), "Duplicate rules!"
    priority_ordering = rule_order
