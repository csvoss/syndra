# Get this file working!

from predicate import Implies, And
from macros import directly_phosphorylates, directly_activates, phosphorylated_is_active

i = directly_phosphorylates("MEK", "ERK")
ii = phosphorylated_is_active("ERK")
iii = directly_activates("MEK", "ERK")

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
