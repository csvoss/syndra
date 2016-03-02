# Get this file working!

from predicate import Implies, And
from macros import directly_phosphorylates, directly_activates, phosphorylated_is_active

i = directly_phosphorylates("MEK", "ERK")
ii = phosphorylated_is_active("ERK")
iii = directly_activates("MEK", "ERK")

pred = Implies(And(i, ii), iii)
assert pred.check_sat()
