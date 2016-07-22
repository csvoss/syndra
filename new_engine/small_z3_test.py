import datatypes
from datatypes import Node, enzyme, substrate
import z3
from contextlib import contextmanager

solver = z3.Solver()

e1 = datatypes.Edge.edge(enzyme, substrate)
e2 = datatypes.Edge.edge(substrate, enzyme)

EdgeSet = z3.ArraySort(datatypes.Edge, z3.BoolSort())

f = z3.Const('f', EdgeSet)

@contextmanager
def context():
    solver.push()
    yield
    solver.pop()

with context():
    print solver.check(), "sat"
    print solver.model()
    solver.add(z3.Select(f, e1))
    print solver.check(), "sat"
    print solver.model()
    solver.add(z3.Not(z3.Select(f, e2)))
    print solver.check(), "sat"
    print solver.model()
    with context():
        solver.add(z3.Not(z3.Select(f, datatypes.Edge.edge(enzyme, substrate))))
        print solver.check(), "unsat"

def new_node(nickname='node'):
    return z3.Const(nickname, Node)

g = z3.Const('testgraph', datatypes.Graph)
n = new_node('testnode1')
n1 = new_node('testnode2')
n2 = new_node('testnode3')
agents = [enzyme, substrate]



# Forall graphs, edge implies has both sides
with context():
    solver.add(z3.ForAll([n1, n2], z3.Implies(z3.Select(datatypes.Graph.links(g), datatypes.Edge.edge(n1, n2)), z3.Select(datatypes.Graph.has(g), n1))))
    print solver.check()
    solver.add(z3.ForAll([n1, n2], z3.Implies(z3.Select(datatypes.Graph.links(g), datatypes.Edge.edge(n1, n2)), z3.Select(datatypes.Graph.has(g), n2))))
    print solver.check()

# Thing in agents implies I have it
with context():
    solver.add(z3.ForAll([n], z3.Implies(z3.Or(*map(lambda a: a==n, agents)), z3.Select(datatypes.Graph.has(g), n))))
    print solver.check()

# Has thing implies it's in agents
with context():
    solver.add(z3.ForAll([g, n], z3.Implies(z3.Select(datatypes.Graph.has(g), n), z3.Or(*map(lambda a: a==n, agents)))))
    print solver.check()


print solver.check(), "sat"
