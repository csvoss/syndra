import z3

from pythonize import pythonized
from solver import solver
import datatypes
from datatypes import new_node
from string_interner import string_interner, node_interner

class Predicate(object):
    def __init__(self):
        raise NotImplementedError("Predicate is an abstract class.")

    def _get_predicate(self, model_variable):
        # returns a z3 predicate
        predicate = self._assert(self.model_variable)
        return predicate

    def _assert(self, model):
        raise NotImplementedError("Implement _assert in subclasses.")


def _ensure_predicate(thing):
    """Raise ValueError if thing is not an instance of Predicate."""
    if not isinstance(thing, Predicate):
        raise ValueError("Argument must be instance of Predicate. Instead, got %s" % repr(thing))


class And(Predicate):
    def __init__(self, *preds):
        for pred in preds:
            _ensure_predicate(pred)
        self.preds = preds

    def _assert(self, model):
        return z3.And(*map(lambda p: p._assert(model),
                           self.preds))

class Not(Predicate):
    def __init__(self, pred):
        _ensure_predicate(pred)
        self.pred = pred

    def _assert(self, model):
        return z3.Not(self.pred._assert(model))

class Or(Predicate):
    def __init__(self, *preds):
        for pred in preds:
            _ensure_predicate(pred)
        self.preds = preds

    def _assert(self, model):
        return z3.Or(*map(lambda p: p._assert(model),
                          self.preds))


class ModelHasRule(Predicate):
    def __init__(self, rule_function):
        self.rule_function = rule_function
        self.rule_variable = None

    def _assert(self, model):
        self.rule_variable = datatypes.new_rule()
        return z3.Exists([self.rule_variable],
            z3.And(model(self.rule_variable),
            self.rule_function(self.rule_variable)
                    ._assert(model)))

class PregraphHas(Predicate):
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure

    def _assert(self, model):
        return self.structure._assert(datatypes.Rule.pregraph(self.rule))

class PostgraphHas(Predicate):
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure

    def _assert(self, model):
        return self.structure._assert(datatypes.Rule.postgraph(self.rule))


class Top(Predicate):
    def __init__(self):
        pass
    def _assert(self, model):
        return z3.Or(True)

class Bottom(Predicate):
    def __init__(self):
        pass
    def _assert(self, model):
        return z3.And(False)
