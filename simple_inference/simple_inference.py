from z3 import Not, And, ForAll, Implies, IntSort, BoolSort, Solver, Function, Int

__counter = 100
__agents = {}
def new_noun(name):
    global __counter
    global __agents
    if name not in __agents:
        __agents[name] = __counter
        __counter += 1
    return Int(__agents[name])

MEK1 = new_noun("MEK1")
ERK1 = new_noun("ERK1")
RAF = new_noun("RAF")
HRAS = new_noun("HRAS")
SAF1 = new_noun("SAF1")

IsKinase = Function("is_kinase", IntSort(), BoolSort())
IsActiveWhenPhosphorylated = Function("is_active_when_phosphorylated", IntSort(), BoolSort())

Phosphorylates = Function("phosphorylates", IntSort(), IntSort(), BoolSort())
Activates = Function("activates", IntSort(), IntSort(), BoolSort())

solver = Solver()

### GENERAL BIOLOGY KNOWLEDGE AXIOMS

# Axiom: y is active when phosphorylated => (x phosphorylates y => x activates y)
x = Int('x')
y = Int('y')
solver.add(ForAll([y], Implies(IsActiveWhenPhosphorylated(y), ForAll([x], Implies(Phosphorylates(x, y), Activates(x, y))))))

# Axiom: If x phosphorylates y, then x is a kinase
solver.add(ForAll([x, y], Implies(Phosphorylates(x, y), IsKinase(x))))

# Axiom: If x is active when phosphorylated, then anything which is true of phosphorylated x is true of activated x

### NETWORK-SPECIFIC KNOWLEDGE

solver.add(IsKinase(MEK1))
solver.add(IsKinase(ERK1))
solver.add(IsKinase(RAF))
solver.add(Not(IsKinase(HRAS)))

solver.add(Phosphorylates(MEK1, ERK1))
solver.add(Phosphorylates(RAF, MEK1))

solver.add(IsActiveWhenPhosphorylated(MEK1))
solver.add(IsActiveWhenPhosphorylated(ERK1))
solver.add(IsActiveWhenPhosphorylated(SAF1))

### SOLVING THE MODEL

print solver.check()
model = solver.model()
print model


### QUERIES

def is_valid(predicate):
    solver.push()
    solver.add(Not(predicate))
    response = solver.check().r
    solver.pop()
    if response > 0:
        return False
    else:
        return True

# Query: Does MEK1 activate ERK1? Yes.
print is_valid(Activates(MEK1, ERK1))

# Query: Does MEK1 activate SAF1? No.
print is_valid(Activates(MEK1, SAF1))
