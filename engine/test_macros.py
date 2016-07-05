import atomic_predicate
import datatypes
from labels import ACTIVE, PHOSPHORYLATED
from macros import directly_phosphorylates, directly_activates, phosphorylated_is_active
import predicate
from solver import solver
import z3

# Sanity checks.
assert not predicate.Bottom().check_sat()
assert predicate.Top().check_sat()
assert not predicate.And(predicate.Bottom(), predicate.Top()).check_sat()
assert not predicate.ForAll(predicate.Bottom()).check_sat()
assert predicate.ForAll(predicate.Top()).check_sat()
assert not predicate.Exists(predicate.Bottom()).check_sat()
assert predicate.Exists(predicate.Top()).check_sat()


print "Predicate I: MEK directly phosphorylates ERK in a single step.\nTranslated to z3:"
i = directly_phosphorylates("MEK", "ERK")
print i.get_predicate()

print "\nPredicate II: ERK, when phosphorylated, is always active.\nTranslated to z3:"
ii = phosphorylated_is_active("ERK")
print ii.get_predicate()

print "\nPredicate III: MEK directly activates ERK in a single step.\nTranslated to z3:"
iii = directly_activates("MEK", "ERK")
print iii.get_predicate()


print "\nEach of these predicates is satisfiable (True) on their own: checking..."
assert i.check_sat()
print i.check_sat()
assert ii.check_sat()
print ii.check_sat()
assert iii.check_sat()
print iii.check_sat()


print "\nI and II are satisfiable together: checking And(I, II)..."
and_i_ii = predicate.And(i, ii)
assert and_i_ii.check_sat()
print and_i_ii.check_sat()

print "\nI and II imply III: checking Implies(And(I, II), III)..."
implication = predicate.Implies(and_i_ii, iii)
assert implication.check_sat()
print implication.check_sat()

print "\nI and II and III are satisfiable together: checking And(I, II, III)..."
and_i_ii_iii = predicate.And(i, ii, iii)
assert and_i_ii_iii.check_sat()
print and_i_ii_iii.check_sat()

print "\nHector's examples"
