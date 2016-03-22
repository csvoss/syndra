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

assert solver.quick_check(i)
assert solver.quick_check(ii)
assert solver.quick_check(iii)

and_i_ii = z3.And(i, ii)
assert solver.quick_check(and_i_ii)

implication = z3.Implies(and_i_ii, iii)
assert solver.quick_check(implication)

and_i_ii_iii = z3.And(i, ii, iii)
assert solver.quick_check(and_i_ii_iii)


# indirectly_activates

# be sure to address in thesis: why not just straight inference rules?
# (answer: easy to introduce inconsistencies, use different definitions
# across different rules)


# x: A activates B
# y: B activates C
# z: A activates C
