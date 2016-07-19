import datatypes
import z3
from contextlib import contextmanager

solver = z3.Solver()

enzyme = z3.Const('enzyme', datatypes.Node)
substrate = z3.Const('substrate', datatypes.Node)
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
    return z3.Const(nickname, datatypes.Node)

g = z3.Const('testgraph', datatypes.Graph)
n = new_node('testnode1')
n1 = new_node('testnode2')
n2 = new_node('testnode3')
agents = [enzyme, substrate]

# Forall graphs, edge implies has both sides
with context():
    solver.add(z3.ForAll([g, n1, n2], z3.Implies(z3.Select(datatypes.Graph.links(g), datatypes.Edge.edge(n1, n2)), z3.Select(datatypes.Graph.has(g), n1))))
    print solver.check()
    solver.add(z3.ForAll([g, n1, n2], z3.Implies(z3.Select(datatypes.Graph.links(g), datatypes.Edge.edge(n1, n2)), z3.Select(datatypes.Graph.has(g), n2))))
    print solver.check()

# Forall graphs, only has the agents I want in it
with context():
    solver.add(z3.ForAll([g, n], z3.Implies(z3.Or(*map(lambda a: a==n, agents)), z3.Select(datatypes.Graph.has(g), n))))
    print solver.check()

with context():
    solver.add(z3.ForAll([g, n], z3.Implies(z3.Select(datatypes.Graph.has(g), n), z3.Or(*map(lambda a: a==n, agents)))))
    print solver.check()


print solver.check(), "sat"
