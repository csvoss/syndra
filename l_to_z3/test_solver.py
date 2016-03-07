import z3

from solver import solver
from unittest import TestCase

z3True = z3.Or(True, True)
z3False = z3.And(False, False)

class SolverTestCase(TestCase):

    def test_true(self):
        self.assertTrue(solver.quick_check(z3True))

    def test_false(self):
        self.assertFalse(solver.quick_check(z3False))

    def test_context(self):
        with solver.context():
            solver.add(z3False)
            self.assertFalse(solver.check())
        self.assertTrue(solver.check())

    def test_quick_check_implied_f_t(self):
        with solver.context():
            solver.add(z3False)
            self.assertTrue(solver.quick_check_implied(z3True))

    def test_quick_check_implied_f_f(self):
        with solver.context():
            solver.add(z3False)
            self.assertTrue(solver.quick_check_implied(z3False))

    def test_quick_check_implied_t_t(self):
        with solver.context():
            solver.add(z3True)
            self.assertTrue(solver.quick_check_implied(z3True))

    def test_quick_check_implied_t_f(self):
        with solver.context():
            solver.add(z3True)
            self.assertFalse(solver.quick_check_implied(z3False))
