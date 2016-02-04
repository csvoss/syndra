"""
L predicate, in the double-bracket semantics. This constrains over sets of
sets of <graph, action> pairs.

Refer to pg. 8 of the L description.
"""

import atomic_predicate
from atomic_predicate import Variable
from model import Node

DEBUG = False

def ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Arguments must be instances of Predicate.")


class Predicate(atomic_predicate.AtomicPredicate):
    def __init__(self, *args):
        super(Predicate, self).__init__(*args)

    # TODO: This is still not right; Predicate
    # should take in a ChemicalSystemSet to quantify over


class PredicateAnd(Predicate):
    """`AND` two L predicates together."""
    def __init__(self, p1, p2, *args):
        super(PredicateAnd, self).__init__(*args)
        ensure_predicate(p1)
        ensure_predicate(p2)
        self.preds = [p1, p2]

    def get_predicate(self):
        for pred in self.preds:
            ensure_predicate(pred)
        return reduce(lambda x, y: x.get_predicate() and y.get_predicate(),
                      self.preds)


class PredicateOr(Predicate):
    """`OR` two L predicates together."""
    def __init__(self, p1, p2, *args):
        super(PredicateOr, self).__init__(*args)
        ensure_predicate(p1)
        ensure_predicate(p2)
        self.preds = [p1, p2]

    def get_predicate(self):
        for pred in self.preds:
            ensure_predicate(pred)
        return reduce(lambda x, y: x.get_predicate() or y.get_predicate(),
                      self.preds)


class PredicateAtomic(Predicate):
    """A predicate that is an atomic predicate."""
    def __init__(self, p, *args):
        super(PredicateAtomic, self).__init__(*args)
        atomic_predicate.ensure_atomic_predicate(p)
        self.pred = p

    def get_predicate(self):
        # forall m. f(m) implies atomic predicate holds over m.
        return self.pred # TODO: this line is incorrect, the above is correct


class PredicateJoin(Predicate):
    """`&` two L predicates together."""
    def __init__(self, p1, p2, *args):
        super(PredicateJoin, self).__init__(*args)
        ensure_predicate(p1)
        ensure_predicate(p2)
        self.preds = [p1, p2]

    def get_predicate(self):
        pass # TODO


class PredicateDontKnow(Predicate):
    """`_\/_` ("don't know" operator) two L predicates together."""
    def __init__(self, p1, p2, *args):
        super(PredicateDontKnow, self).__init__(*args)
        ensure_predicate(p1)
        ensure_predicate(p2)
        self.preds = [p1, p2]

    def get_predicate(self):
        return p1 or p2


class PredicateNot(Predicate):
    """`NOT` an L predicate."""
    def __init__(self, p, *args):
        super(PredicateNot, self).__init__(*args)
        ensure_predicate(p)
        self.pred = import pdb; pdb.set_trace()

    def get_predicate(self):
        pass # TODO


class PredicateForall(Predicate):
    def __init__(self, var, p, *args):
        super(PredicateForall, self).__init__(*args)
        ensure_predicate(p)
        atomic_predicate.ensure_variable(var)
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO


class PredicateExists(Predicate):
    def __init__(self, var, p, *args):
        super(PredicateExists, self).__init__(*args)
        ensure_predicate(p)
        atomic_predicate.ensure_variable(x)
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO
