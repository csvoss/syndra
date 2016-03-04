from unittest import TestCase
import atomic_predicate
import datatypes
import predicate
from solver import solver

class AtomicPredicateTestCase(TestCase):

    def setUp(self):
        self.submodel = datatypes.new_model()
        self.interpretation = datatypes.new_interpretation()

    def test_top_sat(self):
        top = atomic_predicate.Top()
        predicate = top._assert(self.submodel, self.interpretation)
        result = solver.quick_check(predicate)
        self.assertEquals(result, True)

    def test_bottom_unsat(self):
        bottom = atomic_predicate.Bottom()
        predicate = bottom._assert(self.submodel, self.interpretation)
        result = solver.quick_check(predicate)
        self.assertEquals(result, False)


    # TODO: tests for Or, Join, And, DontKnow, Not, Forall, Exists

class PredicateAtomicPredicateTestCase(TestCase):

    def test_top_sat(self):
        status = predicate.Top().check_sat()
        self.assertEquals(status, True)

    def test_bottom_unsat(self):
        status = predicate.Bottom().check_sat()
        self.assertEquals(status, False)
