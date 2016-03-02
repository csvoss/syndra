import atomic_predicate

import solver
import z3


# from datatypes import Graph, Action, Model, Node, Variable
# Placeholders, TODO: uncomment the above once model is working.
Graph = NotImplemented
Action = NotImplemented
Model = NotImplemented



# Predicate and its subclasses.

class Predicate(object):
    def __init__(self):
        raise NotImplementedError("Predicate is an abstract class.")

    def get_model(self):
        # returns a set of sets of <graph, action> pairs, or at the very least
        # something that behaves on the surface as such. It might not
        # necessarily be a complete set. Actions should also behave as sets
        # (sets of atomic actions).
        with solver.context():
            model = Model
            interpretation = z3.Function('interpretation', Variable, Node)
            self._assert(model, interpretation)
            if not solver.check():
                raise ValueError("Tried to get model of unsat predicate")
            return solver.model()
            # TODO: Change the form of this output so that it's what
            # my tests specified: sets, etc. Do that either here or in solver.

    def check_sat(self):
        # returns a boolean
        with solver.context():
            model = Model
            interpretation = z3.Function('interpretation', Variable, Node)
            self._assert(model, interpretation)
            return solver.check()

    def _assert(self, model, interpretation):
        # model is something representing a set of sets of pairs
        # this is only used privately, in check_sat and/or get_model
        raise NotImplementedError("Implement _assert in subclasses.")


class And(Predicate):
    """`AND` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, And)

    def _assert(self, f, interpretation):
        g = Graph('g')
        a = Action('a')
        s = Model('s')
        t = Model('t')
        return z3.Exists([s, t], z3.ForAll([g, a],
                And(self.p1._assert(s), self.p2._assert(t),
                    Iff(f(g, a), s(g, a) and t(g, a)))))


class Or(Predicate):
    """`OR` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, Or)

    def _assert(self, f, interpretation):
        g = Graph('g')
        a = Action('a')
        s = Model('s')
        t = Model('t')
        return z3.Exists([s, t], z3.ForAll([g, a],
                And(self.p1._assert(s), self.p2._assert(t),
                    Iff(f(g, a), s(g, a) or t(g, a)))))


class Join(Predicate):
    """`&` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, Join)

    def _assert(self, f, interpretation):
        g = Graph('g')
        a = Action('a')
        s = Model('s')
        t = Model('t')

        def is_plus(alpha, beta, a):
            # Assert that alpha + beta = a. All of these are Actions.
            # This is defined in Definition 2 of the L paper, on page 5.
            # TODO: implement this once you have a clear API for Action.
            pass

        def is_join(f, s, t, g, a):
            # Assert that f behaves, on inputs g and a, like s "joined" with t.
            # "joined" is the |><| operator.
            alpha = Action('alpha')
            beta = Action('beta')
            return Iff(f(g, a),
                       z3.Exists(alpha, beta),
                       And(s(g, alpha), t(g, beta), is_plus(alpha, beta, a)))

        return z3.Exists([s, t], z3.ForAll([g, a],
                And(self.p1._assert(s), self.p2._assert(t),
                    is_join(f, s, t, g, a))))


class DontKnow(Predicate):
    """`_V_` ("don't know" operator) two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, DontKnow)

    def _assert(self, f, interpretation):
        return self.p1._assert(f) or self.p2._assert(f)


class Not(Predicate):
    """`NOT` an L predicate."""
    def __init__(self, pred):
        self.pred = pred

    def _assert(self, f, interpretation):
        g = Graph('g')
        a = Action('a')
        s = Model('s')
        return z3.Exists([s], z3.ForAll([g, a],
                And(self.pred._assert(s),
                    Iff(f(g, a), not s(g, a)))))


class Forall(Predicate):
    def __init__(self, var, p, *args):
        _ensure_predicate(p)
        _ensure_string(var)
        self.pred = p
        self.var = var

    def _assert(self, f, interpretation):
        pass # TODO


class Exists(Predicate):
    def __init__(self, var, p, *args):
        _ensure_predicate(p)
        _ensure_string(var)
        self.pred = p
        self.var = var

    def _assert(self, f, interpretation):
        pass # TODO


def Implies(predicate1, predicate2):
    # Macro for implies
    return Or(Not(predicate1), predicate2)


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


def _atomic_predicate_wrapper(atomic_predicate_classref):
    # Modify the interpretation of the atomic_predicate so that it
    # behaves as a predicate.
    # Each atomic_predicate implements its own _assert
    class NewClass(Predicate):
        def __init__(self, *args):
            self.atomic = atomic_predicate_classref(*args)

        def _assert(self, f, interpretation):
            # f is a function from g,a to bool
            g = Graph('g')
            a = Action('a')
            return z3.ForAll([g, a],
                    Iff(f(g, a), self.atomic._assert(g, a)))

    return NewClass

def _ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Argument must be instance of Predicate.")


def _ensure_string(thing):
    """Raise ValueError if thing is not a Python string."""
    if not isinstance(thing, str):
        raise ValueError("Argument must be a Python string.")

def Iff(p1, p2):
    return And(Implies(p1, p2), Implies(p2, p1))

# Atomic predicates. This sets the value of a bunch of variables, e.g. Top and
# Add, in this namespace.

for classname in ['Top', 'Bottom', 'Equal', 'PreLabeled', 'PostLabeled',
                  'PostParent', 'DoParent', 'PreLink', 'PostLink',
                  'PostUnlabeled', 'Named', 'PreParent', 'PreUnlabeled',
                  'DoLink', 'DoUnlink', 'PreHas', 'PostHas', 'Add', 'Rem']:
    classref = getattr(atomic_predicate, classname)
    new_classref = _atomic_predicate_wrapper(classref)
    new_classref.__name__ = classname
    globals()[classname] = new_classref
