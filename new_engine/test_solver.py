import predicate
from solver import solver
from unittest import TestCase

syndra_true = predicate.Top()
syndra_false = predicate.Bottom()

class SolverTestCase(TestCase):

    def test_quick_check_true(self):
        self.assertTrue(solver.quick_check(syndra_true))

    def test_quick_check_false(self):
        self.assertFalse(solver.quick_check(syndra_false))

    def test_quick_check_pushes_and_pops(self):
        self.assertTrue(solver.check())
        self.assertFalse(solver.quick_check(syndra_false))
        self.assertTrue(solver.check())

    def test_context(self):
        with solver.context():
            solver.add(syndra_false)
            self.assertFalse(solver.check())
        self.assertTrue(solver.check())

    def test_add(self):
        with solver.context():
            self.assertTrue(solver.check())
            solver.add(syndra_true)
            self.assertTrue(solver.check())
            solver.add(syndra_false)
            self.assertFalse(solver.check())

    def test_quick_check_valid_f_t(self):
        with solver.context():
            solver.add(syndra_false)
            self.assertTrue(solver.quick_check_valid(syndra_true))

    def test_quick_check_valid_f_f(self):
        with solver.context():
            solver.add(syndra_false)
            self.assertTrue(solver.quick_check_valid(syndra_false))

    def test_quick_check_valid_t_t(self):
        with solver.context():
            solver.add(syndra_true)
            self.assertTrue(solver.quick_check_valid(syndra_true))

    def test_quick_check_valid_t_f(self):
        with solver.context():
            solver.add(syndra_true)
            self.assertFalse(solver.quick_check_valid(syndra_false))

    def test_push_pop(self):
        self.assertTrue(solver.check())
        solver.push()
        self.assertTrue(solver.check())
        solver.add(syndra_false)
        self.assertFalse(solver.check())
        solver.pop()
        self.assertTrue(solver.check())
