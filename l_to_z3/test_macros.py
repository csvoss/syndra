# Get this file working!

import atomic_predicate
import datatypes
from labels import ACTIVE, PHOSPHORYLATED
from macros import directly_phosphorylates, directly_activates, phosphorylated_is_active
import predicate
from predicate import Implies, And, Not
from solver import solver
import z3

i = directly_phosphorylates("MEK", "ERK")
ii = phosphorylated_is_active("ERK")
iii = directly_activates("MEK", "ERK")


# Manual Z3 translation of first predicate
g = datatypes.new_graph('g')
a = datatypes.new_action('a')
A = datatypes.new_variable(nickname="MEK")
B = datatypes.new_variable(nickname="ERK")
intp = datatypes.new_interpretation()
subm = predicate.model_from(g, a)

p0 = atomic_predicate.Named(A, "MEK")._assert(subm, intp)
p1 = atomic_predicate.Named(B, "ERK")._assert(subm, intp)

I = z3.Exists([g, a], z3.Implies(p0,
        z3.Implies(p1,
            z3.And(atomic_predicate.PreLabeled(A, ACTIVE)._assert(subm, intp),
                atomic_predicate.PreUnlabeled(B, PHOSPHORYLATED)._assert(subm, intp),
                atomic_predicate.PostLabeled(A, ACTIVE)._assert(subm, intp),
                atomic_predicate.PostLabeled(B, PHOSPHORYLATED)._assert(subm, intp)))))

assert solver.quick_check(I)



# Manual Z3 translation of third predicate
g = datatypes.new_graph('g')
a = datatypes.new_action('a')
A = datatypes.new_variable(nickname="MEK")
B = datatypes.new_variable(nickname="ERK")
intp = datatypes.new_interpretation()
subm = predicate.model_from(g, a)

p0 = atomic_predicate.Named(A, "MEK")._assert(subm, intp)
p1 = atomic_predicate.Named(B, "ERK")._assert(subm, intp)

III = z3.Exists([g, a], z3.Implies(p0,
        z3.Implies(p1,
            z3.And(atomic_predicate.PreLabeled(A, ACTIVE)._assert(subm, intp),
                atomic_predicate.PreUnlabeled(B, ACTIVE)._assert(subm, intp),
                atomic_predicate.PostLabeled(A, ACTIVE)._assert(subm, intp),
                atomic_predicate.PostLabeled(B, ACTIVE)._assert(subm, intp)))))

assert solver.quick_check(III)

raise StandardError("premature quit")

# Implies(And(i, ii), iii): check a theorem over all possible models
pred1 = Implies(And(i, ii), iii)
assert pred1.check_sat() # This should be true.
pred2 = Not(Implies(And(i, ii), iii))
assert pred2.check_sat() # This should be false.

pred3 = And(i, ii, iii)
assert pred3.check_sat() # This should be true.
pred4 = Not(And(i, ii, iii))
assert pred4.check_sat() # This should be true.

# inconsistencies in a model: And(i, ii, iii) and see what happens

# indirectly_activates

# be sure to address in thesis: why not just straight inference rules?
# (answer: easy to introduce inconsistencies, use different definitions
# across different rules)


# x: A activates B
# y: B activates C
# z: A activates C
