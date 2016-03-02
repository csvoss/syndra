from unittest import TestCase
import atomic_predicate

class AtomicPredicateTestCase(TestCase):

    def setUp(self):
        self.top = atomic_predicate.Top()
        self.bottom = atomic_predicate.Bottom()

    def test_top_sat(self):
        status = self.top.check_sat()
        self.assertEquals(status, True)

    def test_bottom_unsat(self):
        status = self.bottom.check_sat()
        self.assertEquals(status, False)

    def test_simple_top_model(self):
        model = self.top.get_model()
        self.assertIsNotNone(model)

    # TODO: tests for Or, Join, And, DontKnow, Not, Forall, Exists
