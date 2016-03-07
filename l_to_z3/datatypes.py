"""Z3 implementation of L - the meta-Kappa devised by Adrien Husson and Jean
Krivine - using the Python bindings for Z3.
"""

from z3 import Datatype, ArraySort, IntSort, BoolSort, Function, Const
from z3_helpers import Iff, Equals



# Node is a datatype representing a vertex or node in a Kappa graph.
Node = Datatype('Node')
Node.declare('node',
    ('unique_identifier', IntSort()))
Node = Node.create()

# A datatype for storing a pair of edges
Edge = Datatype('Edge')
Edge.declare('edge',
    ('node1', Node),
    ('node2', Node))
Edge = Edge.create()

Nodeset = ArraySort(Node, BoolSort())
Edgeset = ArraySort(Edge, BoolSort())

Labelset = ArraySort(IntSort(), BoolSort())
Labelmap = ArraySort(Node, Labelset)

# Graph, before a rule or action has applied. Merged Pregraph and Postgraph
# into a single datatype.
Graph = Datatype('Graph')
Graph.declare('graph',
    ('has', Nodeset),
    ('links', Edgeset),
    ('parents', Edgeset),
    ('labelmap', Labelmap))
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
Variable.declare('variable', ('get_name', IntSort()))
Variable = Variable.create()


def new_thing_function(datatype, default_name):
    def new_thing(nickname=default_name):
        return Const(_collision_free_string(nickname), datatype)
    return new_thing

new_variable = new_thing_function(Variable, 'var')
new_graph = new_thing_function(Graph, 'graph')
new_action = new_thing_function(Action, 'action')
new_model = new_thing_function(Model, 'model')

def new_modelset(nickname='modelset'):
    return Function(_collision_free_string(nickname), Model, BoolSort())

def new_interpretation():
    return Function('interpretation', Variable, Node)


# TODO: Put this whole numbergen and collision-free business into your Solver
# class once you create it

from itertools import count
_numbergen = count(start=100, step=1)

def _collision_free_string(prefix=""):
    return prefix + "_" + str(_numbergen.next())


def _ensure_variable(thing):
    """Raise ValueError if thing is not an instance of z3 Variable."""
    try:
        assert thing.sort() == Variable
    except (AttributeError, AssertionError):
        raise ValueError("Arguments must be z3 instances of Variable. Instead, got %s" % repr(thing))

def _ensure_string(thing):
    """Raise ValueError if thing is not a Python string."""
    if not isinstance(thing, str):
        raise ValueError("Argument must be a Python string. Instead, got %s" % repr(thing))
