import atomic_predicate
import datatypes
from labels import ACTIVE, PHOSPHORYLATED
from macros import directly_phosphorylates, directly_activates, phosphorylated_is_active
import predicate
from predicate import Implies, And, Not
from solver import solver
import z3

print "Predicate I: MEK directly phosphorylates ERK in a single step.\nTranslated to z3:"
i = directly_phosphorylates("MEK", "ERK")
print i

print "\nPredicate II: ERK, when phosphorylated, is always active.\nTranslated to z3:"
ii = phosphorylated_is_active("ERK")
print ii

print "\nPredicate III: MEK directly activates ERK in a single step.\nTranslated to z3:"
iii = directly_activates("MEK", "ERK")
print iii

print "\nEach of these predicates is satisfiable (True) on their own: checking..."
assert solver.quick_check(i)
print solver.quick_check(i)
assert solver.quick_check(ii)
print solver.quick_check(ii)
assert solver.quick_check(iii)
print solver.quick_check(iii)

print "\nI and II are satisfiable together: checking And(I, II)..."
and_i_ii = z3.And(i, ii)
assert solver.quick_check(and_i_ii)
print solver.quick_check(and_i_ii)

print "\nI and II imply III: checking Implies(And(I, II), III)..."
implication = z3.Implies(and_i_ii, iii)
assert solver.quick_check(implication)
print solver.quick_check(implication)

print "\nI and II and III are satisfiable together: checking And(I, II, III)..."
and_i_ii_iii = z3.And(i, ii, iii)
assert solver.quick_check(and_i_ii_iii)
print solver.quick_check(and_i_ii_iii)

print "\nI and not-I are NOT satisfiable together: checking And(I, Not(I))..."
assert not solver.quick_check(z3.And(z3.Not(i), i))
print solver.quick_check(z3.And(z3.Not(i), i))
