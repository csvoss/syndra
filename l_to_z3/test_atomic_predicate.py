from unittest import TestCase
import z3

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

        with solver.context():
            solver.add(pred1._assert(self.submodel, self.interpretation))
            solver.add(pred2._assert(self.submodel, self.interpretation))
            sat = solver.check()
            self.assertTrue(sat)

            solver.add(z3.Not(pred3._assert(self.submodel, self.interpretation)))
            unsat = solver.check()
            self.assertFalse(unsat)

    def test_named_sat(self):
        v = datatypes.new_variable()
        s = "Name"
        pred = atomic_predicate.Named(v, s)
        self.assertSat(pred)

    def test_named_unsat(self):
        v = datatypes.new_variable()
        s1 = "Name 1"
        s2 = "Name 2"
        pred1 = atomic_predicate.Named(v, s1)
        pred2 = atomic_predicate.Named(v, s2)
        status = solver.quick_check(
            z3.And(pred1._assert(self.submodel, self.interpretation),
                   pred2._assert(self.submodel, self.interpretation)))
        self.assertFalse(status)

    def test_named_still_sat(self):
        v = datatypes.new_variable()
        s1 = "Same Name"
        s2 = "Same Name"
        pred1 = atomic_predicate.Named(v, s1)
        pred2 = atomic_predicate.Named(v, s2)
        status = solver.quick_check(
            z3.And(pred1._assert(self.submodel, self.interpretation),
                   pred2._assert(self.submodel, self.interpretation)))
        self.assertTrue(status)

    def test_validity_of_name_implies_name(self):
        v = datatypes.new_variable()
        s1 = "Same Name"
        s2 = "Same Name"
        pred1 = atomic_predicate.Named(v, s1)
        pred2 = atomic_predicate.Named(v, s2)
        with solver.context():
            solver.add(pred1._assert(self.submodel, self.interpretation))
            self.assertTrue(solver.check())
            status = solver.quick_check_implied(
                       pred2._assert(self.submodel, self.interpretation))
            self.assertTrue(status)

    def test_named_get_model(self):
        v = datatypes.new_variable()
        s = "Name"
        pred = atomic_predicate.Named(v, s)
        z3pred = pred._assert(self.submodel, self.interpretation)
        with solver.context():
            solver.add(z3pred)
            model = solver.model()
            self.assertIsNotNone(model[v])
            self.assertEquals(model[v], datatypes.Variable.variable(1))

    def test_prehas_sat(self):
        v = datatypes.new_variable()
        pred = atomic_predicate.PreHas(v)
        self.assertSat(pred)

    def test_posthas_sat(self):
        v = datatypes.new_variable()
        pred = atomic_predicate.PostHas(v)
        self.assertSat(pred)

    def test_add_sat(self):
        v = datatypes.new_variable()
        pred = atomic_predicate.Add(v)
        self.assertSat(pred)

    def test_rem_sat(self):
        v = datatypes.new_variable()
        pred = atomic_predicate.Rem(v)
        self.assertSat(pred)


class AtomicPredicateToPredicateTestCase(TestCase):

    def test_top_sat(self):
        status = predicate.Top().check_sat()
        self.assertTrue(status)

    def test_bottom_unsat(self):
        status = predicate.Bottom().check_sat()
        self.assertFalse(status)
