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

IsKinase = Function("is_kinase", IntSort(), BoolSort())
IsActiveWhenPhosphorylated = Function("is_active_when_phosphorylated", IntSort(), BoolSort())

Phosphorylates = Function("phosphorylates", IntSort(), IntSort(), BoolSort())
Activates = Function("activates", IntSort(), IntSort(), BoolSort())

ActivityIncreasesActivity = Function("activity_increases_activity", IntSort(), IntSort(), BoolSort())

solver = Solver()

MEK1 = new_noun("MEK1")
ERK1 = new_noun("ERK1")
RAF = new_noun("RAF")
HRAS = new_noun("HRAS")
SAF1 = new_noun("SAF1")


### GENERAL BIOLOGY KNOWLEDGE AXIOMS
x = Int('x')
y = Int('y')
z = Int('z')

# Axiom: y is active when phosphorylated => (x phosphorylates y => x activates y)
solver.add(ForAll([y], Implies(IsActiveWhenPhosphorylated(y), ForAll([x], Implies(Phosphorylates(x, y), Activates(x, y))))))

# Axiom: If x phosphorylates y, then x is a kinase
solver.add(ForAll([x, y], Implies(Phosphorylates(x, y), IsKinase(x))))

# Axiom: If x is active when phosphorylated, then anything which is true of phosphorylated x is true of activated x

# Axiom: If x increases activity of y, and y increases activity of z, then x increases activity of z
solver.add(ForAll([x, y, z], Implies(ActivityIncreasesActivity(x, y), Implies(ActivityIncreasesActivity(y, z), ActivityIncreasesActivity(x, z)))))

# Axiom: If x activates y, x increases the activity of y
solver.add(ForAll([x, y], Implies(Activates(x, y), ActivityIncreasesActivity(x, y))))

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

solver.check()
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
    return True

def is_sat(predicate):
    solver.push()
    solver.add(predicate)
    response = solver.check().r
    solver.pop()
    if response > 0:
        return True
    return False

# Query: Does MEK1 activate ERK1? Yes.
print "Should be true:", is_valid(Activates(MEK1, ERK1))

# Query: Does MEK1 activate SAF1? No.
print "Should be false:", is_valid(Activates(MEK1, SAF1))

# Query: Is it possible for HRAS to phosphorylate MEK1? No, it's not a kinase.
print "Should be false:", is_sat(Phosphorylates(HRAS, MEK1))

# Query: Is it possible for RAF to phosphorylate MEK1? Yes.
print "Should be true:", is_sat(Phosphorylates(RAF, MEK1))

# In fact it does; let's add that to the context.
solver.add(Phosphorylates(RAF, MEK1))

# Query: Does RAF activity increase MEK1 and ERK1 activity? Yes.
print "Should be true:", is_valid(ActivityIncreasesActivity(RAF, MEK1))
print "Should be true:", is_valid(ActivityIncreasesActivity(RAF, ERK1))

# Query: Does RAF activity increase SAF1 activity? Not with current info.
print "Should be false:", is_valid(ActivityIncreasesActivity(RAF, SAF1))
