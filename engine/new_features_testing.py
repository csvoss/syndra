

# E. HRAS: agent. E. RAF: agent. E. MEK1: agent. E. ERK1: agent. E. SAF1: agent.
#   (E. r: rule. (HRAS_GTP-RAF in r.LHS) /\ (MEK1 in r.LHS) /\ (MEK1_P in r.RHS) ) /\
#   (E. r: rule. (MEK1_P in r.LHS) /\ (ERK1 in r.LHS) /\ (ERK1_P in r.RHS) ) /\
#   (E. r: rule. (ERK1_P in r.LHS) /\ (SAF1 in r.LHS) /\ (SAF1_P in r.RHS) )

# Datatypes!

import z3
from solver import solver
from string_interner import string_interner


# Node is a datatype representing a vertex or node in a Kappa graph.
Node = z3.Datatype('Node')
Node.declare('node',
    ('unique_identifier', z3.IntSort()))
Node = Node.create()

# A datatype for storing a pair of edges
Edge = z3.Datatype('Edge')
Edge.declare('edge',
    ('node1', Node),
    ('node2', Node))
Edge = Edge.create()

Nodeset = z3.ArraySort(Node, z3.BoolSort())
Edgeset = z3.ArraySort(Edge, z3.BoolSort())

Labelset = z3.ArraySort(z3.IntSort(), z3.BoolSort())
Labelmap = z3.ArraySort(Node, Labelset)

# Graph, before a rule or action has applied. Merged Pregraph and Postgraph
# into a single datatype.
Graph = z3.Datatype('Graph')
Graph.declare('graph',
    ('has', Nodeset),
    ('links', Edgeset),
    ('parents', Edgeset),
    ('labelmap', Labelmap))
Graph = Graph.create()

# This represents a set of possible <pregraph, postgraph> pairs.
Rule = z3.Datatype('Rule')
Rule.declare('rule', ('pregraph', Graph), ('postgraph', Graph))
Rule = Rule.create()

from itertools import count
_numbergen = count(start=1, step=1)

def _collision_free_string(prefix=""):
    return prefix + "_" + str(_numbergen.next())

def new_rule(nickname='rule'):
    return z3.Const(_collision_free_string(nickname), Rule)

def new_model(nickname='model'):
    return z3.Function(_collision_free_string(nickname), Rule, z3.BoolSort())

Variable = z3.Datatype('Variable')
Variable.declare('variable', ('get_name', z3.IntSort()))
Variable = Variable.create()

def new_interpretation():
    return z3.Function('interpretation', z3.IntSort(), Node)

new_rule()
new_model()

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
        model = new_model()
        interpretation = new_interpretation()
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


class And(Predicate):
    def __init__(self, *preds):
        self.p1, self.p2 = _multi_to_binary(preds, And)

    def _assert(self, model, interpretation):
        return z3.And(self.p1._assert(model, interpretation),
                      self.p2._assert(model, interpretation))

class ModelHasRule(Predicate):
    def __init__(self, rule_function):
        self.rule_function = rule_function

    def _assert(self, model, interpretation):
        rule = new_rule()
        return z3.Exists([rule],
            self.rule_function(rule)._assert(model, interpretation))

class PregraphHas(Predicate):
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure

    def _assert(self, model, interpretation):
        return self.structure._assert(Rule.pregraph(self.rule), interpretation)

class PostgraphHas(Predicate):
    def __init__(self, rule, structure):
        self.rule = rule
        self.structure = structure

    def _assert(self, model, interpretation):
        return self.structure._assert(Rule.postgraph(self.rule), interpretation)

class Structure(object):
    def __init__(self):
        raise NotImplementedError("Structure is an abstract class.")

    def _assert(self, graph, interpretation):
        raise NotImplementedError("Implement _assert in subclasses.")

    def bound(self, other_structure):
        # return a new Structure object
        return Bound(self, other_structure)

    def labeled(self, label):
        # return a new Structure object
        return Labeled(self, label)

    def with_site(self, other_structure):
        # return a new Structure object
        return WithSite(self, other_structure)

class Agent(Structure):
    def __init__(self, name):
        self.name = name
        self.name_as_number = string_interner.get_int_or_add(self.name)

    def central_node_label(self):
        return z3.Int(self.name_as_number)

    def _assert(self, graph, interpretation):
        has = Graph.has(graph)
        node = interpretation(self.central_node_label())
        has_node = z3.Select(has, node)
        return has_node

class Bound(Structure):
    def __init__(self, structure_1, structure_2):
        self.structure_1 = structure_1
        self.structure_2 = structure_2

    def central_node_label(self):
        return self.structure_1.central_node_label()

    def _assert(self, graph, interpretation):
        links = Graph.links(graph)
        node_1 = interpretation(self.structure_1.central_node_label())
        node_2 = interpretation(self.structure_2.central_node_label())
        edge = Edge.edge(node_1, node_2)
        has_link = z3.Select(links, edge)
        return z3.And(has_link,
                self.structure_1._assert(graph, interpretation),
                self.structure_2._assert(graph, interpretation))

class WithSite(Structure):
    def __init__(self, structure_1, structure_2):
        self.structure_1 = structure_1
        self.structure_2 = structure_2

    def central_node_label(self):
        return self.structure_1.central_node_label()

    def _assert(self, graph, interpretation):
        parents = Graph.parents(graph)
        node_1 = interpretation(self.structure_1.central_node_label())
        node_2 = interpretation(self.structure_2.central_node_label())
        edge = Edge.edge(node_1, node_2)
        has_parent = z3.Select(parents, edge)
        return z3.And(has_parent,
                self.structure_1._assert(graph, interpretation),
                self.structure_2._assert(graph, interpretation))


class Labeled(Structure):
    def __init__(self, structure, label):
        self.structure = structure
        self.label = label
        self.label_as_number = string_interner.get_int_or_add(self.label)

    def central_node_label(self):
        return self.structure.central_node_label()

    def _assert(self, graph, interpretation):
        labelmap = Graph.labelmap(graph)
        node = interpretation(self.structure.central_node_label())
        labelset = z3.Select(labelmap, node)  # returns a labelset
        label = self.label_as_number
        label_present = z3.Select(labelset, label) # returns a bool
        return z3.And(label_present,
                self.structure._assert(graph, interpretation))


def Label(label_label):
    # just to make sure nobody gets messy with using strings as labels -- use
    # variables as labels instead, so that Python raises an error if you misspell
    return ("label", label_label)


if __name__ == '__main__':
    RAF = Agent("RAF")
    HRAS = Agent("HRAS")
    MEK1 = Agent("MEK1")
    ERK1 = Agent("ERK1")
    SAF1 = Agent("SAF1")
    gtp = Label("GTP")
    phosphate = Label("phosphate")

    predicate = And(
        ModelHasRule(lambda r: And(
                PregraphHas(r, RAF.bound(HRAS.labeled(gtp))),
                PregraphHas(r, MEK1),
                PostgraphHas(r, MEK1.labeled(phosphate))
        )),
        ModelHasRule(lambda r: And(
                PregraphHas(r, MEK1.labeled(phosphate)),
                PregraphHas(r, ERK1),
                PostgraphHas(r, ERK1.labeled(phosphate))
        )),
        ModelHasRule(lambda r: And(
                PregraphHas(r, ERK1.labeled(phosphate)),
                PregraphHas(r, SAF1),
                PostgraphHas(r, SAF1.labeled(phosphate))
        ))
    )

    print predicate.check_sat()
    print predicate.get_model()
