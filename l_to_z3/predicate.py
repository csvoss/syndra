from atomic_predicate import Top, Bottom, Equal, Labeled, PreParent, \
                             PostParent, DoParent, PreLink, PostLink, DoLink, \
                             DoUnlink, PreHas, PostHas, Add, Rem

import solver

class Predicate(object):
    def __init__(self):
        pass # TODO

    def get_model(self):
        # returns a set of sets of <graph, action> pairs, or at the very least
        # something that behaves on the surface as such. It might not
        # necessarily be a complete set. Actions should also behave as sets
        # (sets of atomic actions).
        solver.push()
        solver.add(self.get_predicate())
        if not solver.check():
            raise ValueError("Tried to get model of unsatisfiable predicate")
        output = solver.model()
        solver.pop()
        # TODO: Change the form of this output so that it's what
        # my tests specified.
        return output

    def check_sat(self):
        # returns a boolean
        solver.push()
        solver.add(self.get_predicate())
        output = solver.check()
        solver.pop()
        assert output in (True, False)
        return output

    def get_predicate(self):
        # implement in subclasses
        # returns a Z3-friendly predicate, combining together AtomicPredicates
        raise NotImplementedError("Implement get_predicate in subclasses.")

def ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Argument must be instance of Predicate.")

def ensure_string(thing):
    """Raise ValueError if thing is not a Python string."""
    if not isinstance(thing, str):
        raise ValueError("Argument must be a Python string.")

class And(Predicate):
    """`AND` two L predicates together."""
    def __init__(self, *preds):
        super(And, self).__init__(*args)
        for p in preds:
            ensure_predicate(p)
        self.preds = preds

    def get_predicate(self):
        return reduce(lambda x, y: x.get_predicate() and y.get_predicate(),
                      self.preds)


class Or(Predicate):
    """`OR` two L predicates together."""
    def __init__(self, *preds):
        super(Or, self).__init__(*args)
        for p in preds:
            ensure_predicate(p)
        self.preds = preds

    def get_predicate(self):
        return reduce(lambda x, y: x.get_predicate() or y.get_predicate(),
                      self.preds)

class Join(Predicate):
    """`&` two L predicates together."""
    def __init__(self, *preds):
        super(Join, self).__init__(*args)
        for p in preds:
            ensure_predicate(p)
        self.preds = preds

    def get_predicate(self):
        pass # TODO

class DontKnow(Predicate):
    """`_\/_` ("don't know" operator) two L predicates together."""
    def __init__(self, *preds):
        super(DontKnow, self).__init__(*args)
        for p in preds:
            ensure_predicate(p)
        self.preds = preds

    def get_predicate(self):
        return reduce(lambda x, y: x.get_predicate() or y.get_predicate(),
                      self.preds)

class Not(Predicate):
    """`NOT` an L predicate."""
    def __init__(self, pred):
        super(Not, self).__init__(*args)
        ensure_predicate(pred)
        self.pred = pred

    def get_predicate(self):
        pass # TODO

class Forall(Predicate):
    def __init__(self, var, p, *args):
        super(Forall, self).__init__(*args)
        ensure_predicate(p)
        ensure_string(var)
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO


class Exists(Predicate):
    def __init__(self, var, p, *args):
        super(Exists, self).__init__(*args)
        ensure_predicate(p)
        ensure_string(var)
        self.pred = p
        self.var = var

    def get_predicate(self):
        pass # TODO


def atomic_predicate_wrapper(atomic_predicate_class):
    # Modify the interpretation of the atomic_predicate so that it
    # behaves as a predicate.
    return NotImplemented


# Atomic predicates.
Top = atomic_predicate_wrapper(Top)
Bottom = atomic_predicate_wrapper(Bottom)
Equal = atomic_predicate_wrapper(Equal)
Labeled = atomic_predicate_wrapper(Labeled)
PreParent = atomic_predicate_wrapper(PreParent)
PostParent = atomic_predicate_wrapper(PostParent)
DoParent = atomic_predicate_wrapper(DoParent)
PreLink = atomic_predicate_wrapper(PreLink)
PostLink = atomic_predicate_wrapper(PostLink)
DoLink = atomic_predicate_wrapper(DoLink)
DoUnlink = atomic_predicate_wrapper(DoUnlink)
PreHas = atomic_predicate_wrapper(PreHas)
PostHas = atomic_predicate_wrapper(PostHas)
Add = atomic_predicate_wrapper(Add)
Rem = atomic_predicate_wrapper(Rem)
