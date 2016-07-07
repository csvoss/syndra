import z3

from solver import solver
import datatypes

class Predicate(object):
    def __init__(self):
        raise NotImplementedError("Predicate is an abstract class.")

    def get_model(self):
        with solver.context():
            predicate = self.get_predicate()
            solver.add(predicate)
            if not solver.check():
                raise ValueError("Tried to get model of unsat predicate")
            return solver.model()

    def check_sat(self):
        return solver.quick_check(self.get_predicate())

    def get_predicate(self):
        # returns a z3 predicate
        model = datatypes.new_model()
        interpretation = datatypes.new_interpretation()
        predicate = self._assert(model, interpretation)
        return predicate

    def _assert(self, model, interpretation):
        raise NotImplementedError("Implement _assert in subclasses.")

    def check_implies(self, other_predicate):
        raise NotImplementedError("TODO")


def _ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Argument must be instance of Predicate. Instead, got %s" % repr(thing))

class And(Predicate):
    def __init__(self, *preds):
        for pred in preds:
            _ensure_predicate(pred)
        self.preds = preds

    def _assert(self, model, interpretation):
        return z3.And(*map(lambda p: p._assert(model, interpretation),
                           self.preds))

class Not(Predicate):
    def __init__(self, pred):
        _ensure_predicate(pred)
        self.pred = pred

    def _assert(self, model, interpretation):
        return z3.Not(self.pred._assert(model, interpretation))

class Or(Predicate):
    def __init__(self, *preds):
        for pred in preds:
            _ensure_predicate(pred)
        self.preds = preds

    def _assert(self, model, interpretation):
        return z3.Or(*map(lambda p: p._assert(model, interpretation),
                          self.preds))


class ModelHasRule(Predicate):
    def __init__(self, rule_function):
        self.rule_function = rule_function

    def _assert(self, model, interpretation):
        rule = datatypes.new_rule()
        return z3.Exists([rule],
            self.rule_function(rule)._assert(model, interpretation))

class PregraphHas(Predicate):
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure

    def _assert(self, model, interpretation):
        return self.structure._assert(datatypes.Rule.pregraph(self.rule), interpretation)

class PostgraphHas(Predicate):
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure

    def _assert(self, model, interpretation):
        return self.structure._assert(datatypes.Rule.postgraph(self.rule), interpretation)

class Top(Predicate):
    def __init__(self):
        pass
    def _assert(self, model, interpretation):
        return z3.Or(True)

class Bottom(Predicate):
    def __init__(self):
        pass
    def _assert(self, model, interpretation):
        return z3.And(False)
