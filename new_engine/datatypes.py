import z3


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
