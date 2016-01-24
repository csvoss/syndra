"""Z3 implementation of L - the meta-Kappa devised by Adrien Husson and Jean
Krivine - using the Python bindings for Z3.
"""

from z3 import *
from z3_helpers import *

# TODO: Resolve name collision between model as in Kappa model and model as in
# Z3 model.

# Identifier is a datatype representing a vertex or node in a Kappa graph.
Identifier = Datatype('Identifier')
Identifier.declare('node', ('label', IntSort()))
Identifier = Identifier.create()

# Graph, before a rule or action has applied.
class Pregraph(object):
    def __init__(self):
        self.has = Function('pregraph_has', Identifier, BoolSort())
        self.links = Function('pregraph_links', Identifier, Identifier, BoolSort())
        self.parents = Function('pregraph_parents', Identifier, Identifier, BoolSort())

# Atomic action. An Action is comprised of a set of these.
AtomicAction = Datatype('AtomicAction')
AtomicAction.declare('id_action')
AtomicAction.declare('add_action', ('added', Identifier))
AtomicAction.declare('rem_action', ('removed', Identifier))
AtomicAction.declare('link_action',
    ('link1', Identifier), ('link2', Identifier))
AtomicAction.declare('unlink_action',
    ('unlink1', Identifier), ('unlink2', Identifier))
AtomicAction.declare('parent_action',
    ('parent1', Identifier), ('parent2', Identifier))
AtomicAction.declare('unparent_action',
    ('unparent1', Identifier), ('unparent2', Identifier))
AtomicAction = AtomicAction.create()

# Action: a set of atomic actions.
class Action(object):
    def __init__(self):
        self.has = Function('action_has', AtomicAction, BoolSort())

# Graph, after a rule or action has been applied.
class Postgraph(object):
    def __init__(self, graph, action):
        self.has = Function('postgraph_has', Identifier, BoolSort())
        self.links = Function('postgraph_links', Identifier, Identifier, BoolSort())
        self.parents = Function('postgraph_parents', Identifier, Identifier, BoolSort())

        # Constrain the postgraph's nodes, links, and parent-child relationships
        # appropriately, according to what the graph and action contain.
        i = Const('i', Identifier)
        j = Const('j', Identifier)

        self.assertions = [
            ForAll(i,
                    Iff(self.has(i),
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
                Iff(self.parents(i, j),
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


# This is Kappa's <graph, action> pair, but I've included the postgraph
# (i.e. the graph after applying the action), too, for convenience.
class GraphActionPair(object):
    def __init__(self):
        self.pregraph = Pregraph()
        self.action = Action()
        self.postgraph = Postgraph(self.pregraph, self.action)


# This represents a set of <graph, action> pairs -- our candidate models!
class Model(object):
    def __init__(self):
        self.pairs = ## TODO, Set(GraphActionPair)

    def add_assertions(self, solver):
        """Add, to some z3 solver, the necessary assertions to create
        an instance of this model.

        For now, the only such assertions needed are in the postgraph."""

        for assertion in self.postgraph.assertions:
            solver.add(assertion)
