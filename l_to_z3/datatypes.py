"""Z3 implementation of L - the meta-Kappa devised by Adrien Husson and Jean
Krivine - using the Python bindings for Z3.
"""

from z3 import *
from z3_helpers import *


Labelset = ArraySort(IntSort(), BoolSort())

# Node is a datatype representing a vertex or node in a Kappa graph.
Node = Datatype('Node')
Node.declare('node',
    ('labels', Labelset),
    ('name', IntSort()))
Node = Node.create()

# A datatype for storing a pair of edges
Edge = Datatype('Edge')
Edge.declare('edge',
    ('node1', Node),
    ('node2', Node))
Edge = Edge.create()

Nodeset = ArraySort(Node, BoolSort())
Edgeset = ArraySort(Edge, BoolSort())

# Graph, before a rule or action has applied. Merged Pregraph and Postgraph
# into a single datatype.
Graph = Datatype('Graph')
Graph.declare('graph',
    ('has', Nodeset),
    ('links', Edgeset),
    ('parents', Edgeset))
Graph = Graph.create()

# Atomic action. An Action is comprised of a set of these.
AtomicAction = Datatype('AtomicAction')
AtomicAction.declare('id_action')
AtomicAction.declare('add_action', ('added', Node))
AtomicAction.declare('rem_action', ('removed', Node))
AtomicAction.declare('link_action',
    ('link1', Node), ('link2', Node))
AtomicAction.declare('unlink_action',
    ('unlink1', Node), ('unlink2', Node))
AtomicAction.declare('parent_action',
    ('parent1', Node), ('parent2', Node))
AtomicAction.declare('unparent_action',
    ('unparent1', Node), ('unparent2', Node))
AtomicAction = AtomicAction.create()

# Action: a set of atomic actions.
Action = ArraySort(AtomicAction, BoolSort())


def postgraph_constraints(pregraph, action, postgraph):
    """
    Create a list of assertions that constrain the postgraph's nodes, links, and
    parent-child relationships appropriately, according to what the graph and
    action contain.
    """
    i = Const('i', Node)
    j = Const('j', Node)

    assertions = [
        ForAll(i,
                Iff(postgraph.has(i),
                    Or(And(graph.has(i), Not(action.has(AtomicAction.rem_action(i)))),
                       action.has(AtomicAction.add_action(i))))),
        ForAll([i, j],
            Iff(self.links(i, j),
                Or(
                    And(
                        And(
                            graph.links(i, j),
                            Not(action.has(AtomicAction.unlink_action(i, j)))),
                        And(
                            Not(action.has(AtomicAction.rem_action(i))),
                            Not(action.has(AtomicAction.rem_action(j))))),
                    action.has(AtomicAction.link_action(i, j))))),
        ForAll([i, j],
            Iff(postgraph.parents(i, j),
                Or(
                    And(
                        And(
                            graph.parents(i, j),
                            Not(action.has(AtomicAction.unparent_action(i, j)))),
                        And(
                            Not(action.has(AtomicAction.rem_action(i))),
                            Not(action.has(AtomicAction.rem_action(j))))),
                        action.has(AtomicAction.parent_action(i, j)))))
    ]

    return assertions


# This represents a set of possible <graph, action> pairs -- a single Kappa
# chemical system or model.
Model = Datatype('Model')
Model.declare('model', ('pregraph', Graph),
                        ('action', Action), ('postgraph', Graph))
Model = Model.create()

# This represents a set of sets of <graph, action> pairs -- many possible
# chemical systems that an L statement could represent.
ModelSet = Function('possible_system', Model, BoolSort())


Variable = Datatype('Variable')
Variable.declare('variable', ('get_varname', IntSort()))
Variable = Variable.create()
