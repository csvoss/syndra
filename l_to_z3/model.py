"""Z3 implementation of L - the meta-Kappa devised by Adrien Husson and Jean
Krivine - using the Python bindings for Z3.
"""

from z3 import *
from z3_helpers import *

# TODO: Make everything in this file a z3 datatype with some helper functions
# lying around; make nothing a Python class. It's easier to keep them
# all in order that way.

# Then, it's easier to implement some of the remaining Predicates.

# Node is a datatype representing a vertex or node in a Kappa graph.
Node = Datatype('Node')
Node.declare('node', ('label', IntSort()))
Node = Node.create()

# Graph, before a rule or action has applied.
class Pregraph(object):
    def __init__(self):
        self.has = Function('pregraph_has', Identifier, BoolSort())
        self.links = Function('pregraph_links', Identifier, Identifier, BoolSort())
        self.parents = Function('pregraph_parents', Identifier, Identifier, BoolSort())

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
class Action(object):
    def __init__(self):
        self.has = Function('action_has', AtomicAction, BoolSort())

# Graph, after a rule or action has been applied.
class Postgraph(object):
    def __init__(self, graph, action):
        self.has = Function('postgraph_has', Node, BoolSort())
        self.links = Function('postgraph_links', Node, Node, BoolSort())
        self.parents = Function('postgraph_parents', Node, Node, BoolSort())

        # Constrain the postgraph's nodes, links, and parent-child relationships
        # appropriately, according to what the graph and action contain.
        i = Const('i', Node)
        j = Const('j', Node)

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

    def initialize(self, solver):
        """Add, to some z3 solver, the necessary assertions to create
        an instance of this model.

        For now, the only such assertions needed are in the postgraph."""

        for assertion in self.postgraph.assertions:
            solver.add(assertion)

# This represents a set of possible <graph, action> pairs -- a single Kappa
# chemical system.
ChemicalSystem = Datatype('ChemicalSystem')
ChemicalSystem.declare('chemicalsystem', ('pregraph', Pregraph),
                        ('action', Action), ('postgraph', Postgraph))
ChemicalSystem = ChemicalSystem.create()


# This represents a set of sets of <graph, action> pairs -- many possible
# chemical systems that an L statement could represent.
def new_model():
    return Function('contains', ChemicalSystem, BoolSort())
