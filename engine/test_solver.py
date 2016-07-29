import predicate
from solver import MySolver
from unittest import TestCase

syndra_true = predicate.Top()
syndra_false = predicate.Bottom()

class SolverTestCase(TestCase):

    def setUp(self):
        self.solver = MySolver("A", "B")

    def test_quick_check_true(self):
        self.assertTrue(self.solver.quick_check(syndra_true))

    def test_quick_check_false(self):
        self.assertFalse(self.solver.quick_check(syndra_false))

    def test_quick_check_pushes_and_pops(self):
        self.assertTrue(self.solver.check())
        self.assertFalse(self.solver.quick_check(syndra_false))
        self.assertTrue(self.solver.check())

    def test_context(self):
        with self.solver.context():
            self.solver.add(syndra_false)
            self.assertFalse(self.solver.check())
        self.assertTrue(self.solver.check())

    def test_add(self):
        with self.solver.context():
            self.assertTrue(self.solver.check())
            self.solver.add(syndra_true)
            self.assertTrue(self.solver.check())
            self.solver.add(syndra_false)
            self.assertFalse(self.solver.check())

    def test_quick_check_valid_f_t(self):
        with self.solver.context():
            self.solver.add(syndra_false)
            self.assertTrue(self.solver.quick_check_valid(syndra_true))

    def test_quick_check_valid_f_f(self):
        with self.solver.context():
            self.solver.add(syndra_false)
            self.assertTrue(self.solver.quick_check_valid(syndra_false))

    def test_quick_check_valid_t_t(self):
        with self.solver.context():
            self.solver.add(syndra_true)
            self.assertTrue(self.solver.quick_check_valid(syndra_true))

    def test_quick_check_valid_t_f(self):
        with self.solver.context():
            self.solver.add(syndra_true)
            self.assertFalse(self.solver.quick_check_valid(syndra_false))

    def test_push_pop(self):
        self.assertTrue(self.solver.check())
        self.solver.push()
        self.assertTrue(self.solver.check())
        self.solver.add(syndra_false)
        self.assertFalse(self.solver.check())
        self.solver.pop()
        self.assertTrue(self.solver.check())
