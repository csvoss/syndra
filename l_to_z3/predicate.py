class Predicate(object):
    def __init__(self):
        pass

    def get_model(self):
        # returns a set of sets of <graph, action> pairs, or at the very least
        # something that behaves on the surface as such. It might not
        # necessarily be a complete set. Actions should also behave as sets
        # (sets of atomic actions).
        pass

    def check_sat(self):
        # returns a boolean
        pass

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
        for pred in self.preds:
            ensure_predicate(pred)
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
        for pred in self.preds:
            ensure_predicate(pred)
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
        return p1 or p2

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


# From atomic_predicate, must import or re-wrap at least the following:
# Labeled
# PreParent
# DoLink
# Top
# Bottom
