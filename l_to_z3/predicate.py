"""
L predicate, in the double-bracket semantics. This constrains over sets of
sets of <graph, action> pairs.

Refer to pg. TODO of the L description.
"""

import atomic_predicate
from atomic_redicate import Variable
from model import Node

DEBUG = False

def ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Arguments must be instances of Predicate.")


class Predicate(object):
    def __init__(self, model):
        self.solver = Solver()
        raise StandardError("Fix the thing with only instantiating one Solver")
        self.model = model
        self.interpretation = Function('interpretation', Variable, Node)
        self._asserted_yet = False
        self._status = None
        self.model.initialize(self.solver)

    def get_predicate(self):
        raise NotImplementedError("Implement get_predicate in subclasses.")

    def _assert_over(self):
        self.solver.add(self.get_predicate())
        self._status = self.solver.check()

        self._asserted_yet = True

    def check_sat(self):
        if not self._asserted_yet:
            self._assert_over()
        if DEBUG:
            print self._status
        return self._status

    def get_model(self):
        """Raises Z3Exception if the model is not available."""
        if not self._asserted_yet:
            self._assert_over()
        output = self.solver.model()
        if DEBUG:
            print output
        return output


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
        return self.pred # TODO: doublecheck this logic


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
        pass # TODO


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
        # TODO ensure var is a Variable
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO


class PredicateExists(Predicate):
    def __init__(self, var, p, *args):
        super(PredicateExists, self).__init__(*args)
        ensure_predicate(p)
        # TODO ensure var is a Variable
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO
