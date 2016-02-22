from atomic_predicate import Top, Bottom, Equal, Labeled, PreParent, \
                             PostParent, DoParent, PreLink, PostLink, DoLink, \
                             DoUnlink, PreHas, PostHas, Add, Rem

import solver



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
            model = NotImplemented
            self._assert(model)
            if not solver.check():
                raise ValueError("Tried to get model of unsat predicate")
            return solver.model()
            # TODO: Change the form of this output so that it's what
            # my tests specified: sets, etc. Do that either here or in solver.

    def check_sat(self):
        # returns a boolean
        with solver.context():
            model = NotImplemented
            self._assert(model)
            return solver.check()

    def _assert(self, model):
        # model is something representing a set of sets of pairs
        # this is only used privately, in check_sat and/or get_model
        raise NotImplementedError("Implement _assert in subclasses.")


class And(Predicate):
    """`AND` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, And)

    def get_predicate(self):
        return reduce(lambda x, y: x.get_predicate() and y.get_predicate(),
                      self.preds)


class Or(Predicate):
    """`OR` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, Or)

    def get_predicate(self):
        return reduce(lambda x, y: x.get_predicate() or y.get_predicate(),
                      self.preds)


class Join(Predicate):
    """`&` two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, Join)

    def get_predicate(self):
        pass # TODO


class DontKnow(Predicate):
    """`_V_` ("don't know" operator) two L predicates together."""
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, DontKnow)

    def get_predicate(self):
        return reduce(lambda x, y: x.get_predicate() or y.get_predicate(),
                      self.preds)


class Not(Predicate):
    """`NOT` an L predicate."""
    def __init__(self, pred):
        self.p1, self.p2 = _multi_to_binary(preds, Not)

    def get_predicate(self):
        pass # TODO


class Forall(Predicate):
    def __init__(self, var, p, *args):
        _ensure_predicate(p)
        _ensure_string(var)
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO


class Exists(Predicate):
    def __init__(self, var, p, *args):
        _ensure_predicate(p)
        _ensure_string(var)
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO



# Private helper functions.

def _multi_to_binary(preds, classref):
    assert len(preds) >= 2,
        "Cannot apply %s to one predicate only" % str(classref)
    for p in preds:
        _ensure_predicate(p)

    p1 = preds[0]
    if len(preds) == 2:
        p2 = preds[1]
    else:
        p2 = classref(preds[1:])

    return (p1, p2)


def _atomic_predicate_wrapper(atomic_predicate_classref):
    # Modify the interpretation of the atomic_predicate so that it
    # behaves as a predicate.
    return NotImplemented


def _ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Argument must be instance of Predicate.")


def _ensure_string(thing):
    """Raise ValueError if thing is not a Python string."""
    if not isinstance(thing, str):
        raise ValueError("Argument must be a Python string.")



# Atomic predicates.

Top = _atomic_predicate_wrapper(Top)
Bottom = _atomic_predicate_wrapper(Bottom)
Equal = _atomic_predicate_wrapper(Equal)
Labeled = _atomic_predicate_wrapper(Labeled)
PreParent = _atomic_predicate_wrapper(PreParent)
PostParent = _atomic_predicate_wrapper(PostParent)
DoParent = _atomic_predicate_wrapper(DoParent)
PreLink = _atomic_predicate_wrapper(PreLink)
PostLink = _atomic_predicate_wrapper(PostLink)
DoLink = _atomic_predicate_wrapper(DoLink)
DoUnlink = _atomic_predicate_wrapper(DoUnlink)
PreHas = _atomic_predicate_wrapper(PreHas)
PostHas = _atomic_predicate_wrapper(PostHas)
Add = _atomic_predicate_wrapper(Add)
Rem = _atomic_predicate_wrapper(Rem)
