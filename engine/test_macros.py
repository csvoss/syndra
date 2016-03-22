import atomic_predicate
import datatypes
from labels import ACTIVE, PHOSPHORYLATED
from macros import directly_phosphorylates, directly_activates, phosphorylated_is_active
import predicate
from predicate import Implies, And, Not
from solver import solver
import z3

print "Predicate 1: MEK directly phosphorylates ERK in a single step"
i = directly_phosphorylates("MEK", "ERK")

print "Predicate 2: ERK, when phosphorylated, is always active"
ii = phosphorylated_is_active("ERK")

print "Predicate 3: MEK directly activates ERK in a single step"
iii = directly_activates("MEK", "ERK")

print "\nEach of these predicates is satisfiable (True) on their own:"
assert solver.quick_check(i)
print solver.quick_check(i)
assert solver.quick_check(ii)
print solver.quick_check(ii)
assert solver.quick_check(iii)
print solver.quick_check(iii)

print "\n1 and 2 are satisfiable together:"
and_i_ii = z3.And(i, ii)
assert solver.quick_check(and_i_ii)
print solver.quick_check(and_i_ii)

print "\n1 and 2 imply 3:"
implication = z3.Implies(and_i_ii, iii)
assert solver.quick_check(implication)
print solver.quick_check(implication)

print "\n1 and 2 and 3 are satisfiable together:"
and_i_ii_iii = z3.And(i, ii, iii)
assert solver.quick_check(and_i_ii_iii)
print solver.quick_check(and_i_ii_iii)
