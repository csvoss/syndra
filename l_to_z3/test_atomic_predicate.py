import z3

from unittest import TestCase
import atomic_predicate
import datatypes
import predicate
from solver import solver

class AtomicPredicateTestCase(TestCase):

    def setUp(self):
        self.submodel = datatypes.new_model()
        self.interpretation = datatypes.new_interpretation()

    def assertSat(self, pred):
        asserted = pred._assert(self.submodel, self.interpretation)
        check = solver.quick_check(asserted)
        self.assertTrue(check)

    def assertUnsat(self, pred):
        asserted = pred._assert(self.submodel, self.interpretation)
        check = solver.quick_check(asserted)
        self.assertFalse(check)

    def test_top_sat(self):
        pred = atomic_predicate.Top()
        self.assertSat(pred)

    def test_bottom_unsat(self):
        pred = atomic_predicate.Bottom()
        self.assertUnsat(pred)

    def test_equal_sat(self):
        v1 = datatypes.new_variable()
        v2 = datatypes.new_variable()
        pred = atomic_predicate.Equal(v1, v2)
        self.assertSat(pred)

    def test_equal_transitive(self):
        v1 = datatypes.new_variable()
        v2 = datatypes.new_variable()
        v3 = datatypes.new_variable()
        pred1 = atomic_predicate.Equal(v1, v2)
        pred2 = atomic_predicate.Equal(v2, v3)
        pred3 = atomic_predicate.Equal(v1, v3)

        solver.push()

        solver.add(pred1._assert(self.submodel, self.interpretation))
        solver.add(pred2._assert(self.submodel, self.interpretation))
        sat = solver.check()
        self.assertTrue(sat)

        solver.add(z3.Not(pred3._assert(self.submodel, self.interpretation)))
        unsat = solver.check()
        self.assertFalse(unsat)

        solver.pop()

    



    # TODO: tests for Or, Join, And, DontKnow, Not, Forall, Exists

class PredicateAtomicPredicateTestCase(TestCase):

    def test_top_sat(self):
        status = predicate.Top().check_sat()
        self.assertEquals(status, True)

    def test_bottom_unsat(self):
        status = predicate.Bottom().check_sat()
        self.assertEquals(status, False)
