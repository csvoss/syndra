"""
predicate.py stores a number of classes subclassing Predicate, the base
class of any Syndra predicate.
"""
import z3


class Predicate(object):
    """An abstract class for defining Syndra predicates."""
    def get_predicate(self, model_variable, solver):
        """Converts this Syndra predicate into a z3 predicate.

        Called by the solver in solver.py; should only be used there. Interact
        with Syndra predicates by adding them to the solver -- consult the
        documentation in solver.py.

        Arguments:
            model_variable :: z3 function from Rule to BoolSort

        Returns :: z3 predicate.
        """
        predicate = self._assert(model_variable, solver)
        return predicate
    def _assert(self, model, solver):
        raise NotImplementedError("Implement _assert in subclasses.")


def _ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Argument must be instance of Predicate. Instead, got %s" % repr(thing))


class And(Predicate):
    """Apply logical 'and' to one or more Syndra predicates."""
    def __init__(self, *preds):
        for pred in preds:
            _ensure_predicate(pred)
        self.preds = preds
    def _assert(self, model, solver):
        return z3.And(*[p._assert(model, solver) for p in self.preds])


class Not(Predicate):
    """Apply logical 'not' to a Syndra predicate."""
    def __init__(self, pred):
        _ensure_predicate(pred)
        self.pred = pred
    def _assert(self, model, solver):
        return z3.Not(self.pred._assert(model, solver))


class Or(Predicate):
    """Apply logical 'or' to one or more Syndra predicates."""
    def __init__(self, *preds):
        for pred in preds:
            _ensure_predicate(pred)
        self.preds = preds
    def _assert(self, model, solver):
        return z3.Or(*[p._assert(model, solver) for p in self.preds])


class ModelHasRule(Predicate):
    """Claims that a model has a rule satisfying the given properties.

    Constructor arguments:
        rule_function :: Rule -> Predicate

    For example, if I want to assert that a model has a simple rule that only
    needs to have MEK on the left hand side:

    ModelHasRule(lambda r: And(PregraphHas(r, kinase)))

    TODO: make the "lambda r" part no longer necessary by coding
    PregraphHas and PostgraphHas to auto-insert the rule they need
    """
    def __init__(self, rule_function):
        self.rule_function = rule_function
        self.rule_variable = None
    def _assert(self, model, solver):
        self.rule_variable = solver.new_rule()
        return z3.Exists([self.rule_variable],
                         z3.And(model(self.rule_variable),
                                self.rule_function(self.rule_variable)
                                ._assert(model, solver)))


class PregraphHas(Predicate):
    """Claims that some rule's pregraph has a given structure."""
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure
    def _assert(self, model, solver):
        return self.structure._assert(solver.Rule.pregraph(self.rule), solver)


class PostgraphHas(Predicate):
    """Claims that some rule's postgraph has a given structure."""
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure
    def _assert(self, model, solver):
        return self.structure._assert(solver.Rule.postgraph(self.rule), solver)


class Top(Predicate):
    """Syndra predicate that is always satisfiable."""
    def __init__(self):
        pass
    def _assert(self, model, solver):
        return z3.Or(True)


class Bottom(Predicate):
    """Syndra predicate that is never satisfiable."""
    def __init__(self):
        pass
    def _assert(self, model, solver):
        return z3.And(False)
