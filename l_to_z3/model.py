"""Z3 implementation of L - the meta-Kappa devised by Adrien Husson and Jean
Krivine - using the Python bindings for Z3.
"""

from z3 import *

# Helper function not defined by Z3.
def Iff(a, b):
    return Not(Xor(a, b))


# Identifier is a datatype representing a vertex or node in a Kappa graph.
Identifier = Datatype('Identifier')
Identifier.declare('none')
Identifier.declare('node', ('label', IntSort()))
Identifier = Identifier.create()

# Graph, before a rule or action has applied.
class Pregraph(object):
    def __init__(self):
        self.has = Function('has', Identifier, BoolSort())
        self.links = Function('links', Identifier, Identifier, BoolSort())
        self.parents = Function('parents', Identifier, Identifier, BoolSort())

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
        self.has = Function('has', AtomicAction, BoolSort())

# Graph, after a rule or action has been applied.
class Postgraph(object):
    def __init__(self, graph, action):
        self.has = Function('has', Identifier, BoolSort())
        self.links = Function('links', Identifier, Identifier, BoolSort())
        self.parents = Function('parents', Identifier, Identifier, BoolSort())

        # Constrain the postgraph's nodes, links, and parent-child relationships
        # appropriately, according to what the graph and action contain.
        i = Const('i', Identifier)
        engine.z3_assert(ForAll(Const('i', Identifier),
                                Iff(self.has(i),
                                    Or(And(graph.has(i), Not(action.has(AtomicAction.rem_action(i)))),
                                       action.has(AtomicAction.add_action(i))))))
        engine.z3_assert(ForAll([Const('a', Identifier), Const('b', Identifier)],
            Iff(self.links(a, b),
                Or(
                    And(
                        And(
                            graph.links(a, b),
                            Not(action.has(AtomicAction.unlink_action(a, b)))),
                        And(
                            Not(action.has(AtomicAction.rem_action(a))),
                            Not(action.has(AtomicAction.rem_action(b))))),
                    action.has(AtomicAction.link_action(a, b))))))
        engine.z3_assert(ForAll([Const('a', Identifier), Const('b', Identifier)],
            Iff(self.parents(a, b),
                Or(
                    And(
                        And(
                            graph.parents(a, b),
                            Not(action.has(AtomicAction.unparent_action(a, b)))),
                        And(
                            Not(action.has(AtomicAction.rem_action(a))),
                            Not(action.has(AtomicAction.rem_action(b))))),
                        action.has(AtomicAction.parent_action(a, b))))))


# Model is Kappa's <graph, action> pair, but I've included the postgraph
# (i.e. the graph after applying the action), too, for convenience.
class Model(object):
    def __init__(self):
        self.pregraph = Pregraph()
        self.action = Action()
        self.postgraph = Postgraph(self.pregraph, self.action)
