import z3

import atomic_predicate
from datatypes import _ensure_variable, _ensure_string
from datatypes import Node, Variable, Model, Submodel
from datatypes import new_graph, new_action, new_modelset, new_interpretation
from solver import solver
import z3_helpers


# Predicate and its subclasses.

DEBUG = True

class Predicate(object):
    def __init__(self):
        raise NotImplementedError("Predicate is an abstract class.")

    def get_model(self):
        # returns a set of sets of <graph, action> pairs, or at the very least
        # something that behaves on the surface as such. It might not
        # necessarily be a complete set. Actions should also behave as sets
        # (sets of atomic actions).
        with solver.context():
            predicate = self.get_predicate()
            solver.add(predicate)
            if not solver.check():
                raise ValueError("Tried to get model of unsat predicate")
            return solver.model()

    def check_sat(self):
        # returns a boolean
        return solver.quick_check(self.get_predicate())

    def get_predicate(self):
        # returns a z3 predicate
        modelset = new_modelset()
        interpretation = new_interpretation()
        predicate = self._assert(modelset, interpretation, None, None)
        return predicate

    def _assert(self, modelset, i, g, a):
        # model is something representing a set of sets of pairs
        # this is only used privately, in check_sat and/or get_model
        raise NotImplementedError("Implement _assert in subclasses.")

    def check_implies(self, other_predicate):
        # check that this predicate implies other_predicate
        p1 = self.get_predicate()
        p2 = other_predicate.get_predicate()
        pred = z3.Implies(p1, p2)
        return solver.quick_check(pred)


def has(modelset, g, a):
    postgraph = new_graph('postgraph')
    return z3.Exists([postgraph], modelset(Model.model(g, a, postgraph)))


def model_from(g, a):
    return Submodel(g, a, new_graph('postgraph'))


class ForAll(Predicate):
    def __init__(self, pred):
        self.pred = pred

    def _assert(self, modelset, i, g, a):
        g = new_graph('g')
        a = new_action('a')
        return z3.ForAll([g, a], self.pred._assert(modelset, i, g, a))

class Exists(Predicate):
    def __init__(self, pred):
        self.pred = pred

    def _assert(self, modelset, i, g, a):
        g = new_graph('g')
        a = new_action('a')
        return z3.Exists([g, a], self.pred._assert(modelset, i, g, a))

class And(Predicate):
    """`AND` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, And)

    def _assert(self, modelset, i, g, a):
        return z3.And(self.p1._assert(modelset, i, g, a),
                      self.p2._assert(modelset, i, g, a))


class Or(Predicate):
    """`OR` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, Or)

    def _assert(self, modelset, i, g, a):
        return z3.Or(self.p1._assert(modelset, i, g, a),
                     self.p2._assert(modelset, i, g, a))


class Join(Predicate):
    """`&` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, Join)

    def _assert(self, modelset, i, g, a):
        g = new_graph('g')
        a = new_action('a')
        s = new_modelset('s')
        t = new_modelset('t')

        def is_plus(alpha, beta, a):
            # Assert that alpha + beta = a. All of these are Actions.
            # This is defined in Definition 2 of the L paper, on page 5.
            # TODO: implement this once you have a clear API for Action.
            pass

        def is_join(modelset, s, t, g, a):
            # Assert that modelset behaves, on inputs g and a, like s "joined" with t.
            # "joined" is the |><| operator.
            alpha = Action('alpha')
            beta = Action('beta')
            return z3_helpers.Iff(has(modelset, g, a),
                       z3.Exists(alpha, beta),
                       z3.And(has(s, g, alpha), has(t, g, beta), is_plus(alpha, beta, a)))

        return z3.ForAll([g, a],
                z3.And(self.p1._assert(s, i, g, a), self.p2._assert(t, i, g, a),
                    is_join(modelset, s, t, g, a)))


class DontKnow(Predicate):
    """`_V_` ("don't know" operator) two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, DontKnow)

    def _assert(self, modelset, i, g, a):
        return z3.Or(self.p1._assert(modelset, i, g, a),
                     self.p2._assert(modelset, i, g, a))


class Not(Predicate):
    """`NOT` an L predicate."""
    def __init__(self, pred):
        self.pred = pred

    def _assert(self, modelset, i, g, a):
        return z3.Not(self.pred._assert(modelset, i, g, a))


class Implies(Predicate):
    def __init__(self, p1, p2):
        self.p1 = p1
        self.p2 = p2

    def _assert(self, modelset, i, g, a):
        return z3.Implies(self.p1._assert(modelset, i, g, a),
                          self.p2._assert(modelset, i, g, a))


# Private helper functions.

def _multi_to_binary(preds, classref):
    assert len(preds) >= 2, ("Cannot apply %s to one predicate only" %
                             str(classref))
    for p in preds:
        _ensure_predicate(p)

    p1 = preds[0]
    if len(preds) == 2:
        p2 = preds[1]
    else:
        assert len(preds[1:]) >= 2
        p2 = classref(*preds[1:])

    return (p1, p2)


def _wrapped_atomic_predicate(classname):
    classref = getattr(atomic_predicate, classname)

    # Modify the interpretation of the atomic_predicate so that it
    # behaves as a predicate.
    # Each atomic_predicate implements its own _assert
    class NewClass(Predicate):
        def __init__(self, *args):
            self.atomic = classref(*args)

        def _assert(self, modelset, i, g, a):
            # model is a function from g,a to bool (as an array)
            subpredicate = self.atomic._assert(model_from(g, a), i)
            return subpredicate

    NewClass.__name__ = classname
    return NewClass


# Atomic predicates. This sets the value of a bunch of variables, e.g. Top and
# Add, in this namespace.

for classname in ['Top', 'Bottom', 'Equal', 'PreLabeled', 'PostLabeled',
                  'PostParent', 'DoParent', 'PreLink', 'PostLink',
                  'PostUnlabeled', 'Named', 'PreParent', 'PreUnlabeled',
                  'DoLink', 'DoUnlink', 'PreHas', 'PostHas', 'Add', 'Rem']:
    new_classref = _wrapped_atomic_predicate(classname)
    globals()[classname] = new_classref


def _ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Argument must be instance of Predicate. Instead, got %s" % repr(thing))
