import z3

from pythonize import pythonized
from solver import solver
import datatypes
from string_interner import string_interner

class Predicate(object):
    def __init__(self):
        raise NotImplementedError("Predicate is an abstract class.")

    # TODO deprecate get_model, get_python_model, check_sat. These should
    # all be managed by the Syndra solver (solver.py) instead.

    def get_model(self):
        with solver.context():
            solver.add(self)
            if not solver.check():
                raise ValueError("Tried to get model of unsat predicate")

            # MODEL PRUNING: EDGES
            # For each edge in each graph, assert that that edge isn't there.
            # If we're still satisfiable, continue. Else, pop.
            mo = solver.model()
            interp_variable = self.interpretation_variable
            rules = [i[0] for i in mo[self.model_variable].as_list()[:-1]]

            agents = [j for i, j in string_interner._str_to_int.items() if 'label_' not in i]
            edge_assertions = []
            for rule in rules:
                prg = datatypes.Rule.pregraph(rule)
                pog = datatypes.Rule.postgraph(rule)
                prlinks = datatypes.Graph.links(prg)
                prparents = datatypes.Graph.parents(prg)
                polinks = datatypes.Graph.links(pog)
                poparents = datatypes.Graph.parents(pog)
                for value_1 in agents:
                    for value_2 in agents:
                        edge = datatypes.Edge.edge(interp_variable(value_1), interp_variable(value_2))
                        edge_assertions.append(z3.Not(z3.Select(prparents, edge)))
                        edge_assertions.append(z3.Not(z3.Select(poparents, edge)))
                        edge_assertions.append(z3.Not(z3.Select(prlinks, edge)))
                        edge_assertions.append(z3.Not(z3.Select(polinks, edge)))

            for edge_assertion in edge_assertions:
                solver.push()
                solver.add_z3(edge_assertion)
                satisfiable = solver.check()
                solver.pop()
                if satisfiable:
                    solver.add_z3(edge_assertion)

            # MODEL PRUNING: LABELS
            # TODO

            # MODEL PRUNING: NODES
            # TODO

            assert solver.check()
            return solver.model()

    def get_python_model(self):
        model = self.get_model()
        return pythonized(self, model)

    def check_sat(self):
        return solver.quick_check(self)

    def get_predicate(self):
        # returns a z3 predicate
        self.model_variable = datatypes.new_model()
        self.interpretation_variable = datatypes.new_interpretation()
        predicate = self._assert(self.model_variable,
                                 self.interpretation_variable)
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
        self.rule_variable = None

    def _assert(self, model, interpretation):
        self.rule_variable = datatypes.new_rule()
        return z3.Exists([self.rule_variable],
            z3.And(model(self.rule_variable),
            self.rule_function(self.rule_variable)
                    ._assert(model, interpretation)))

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
