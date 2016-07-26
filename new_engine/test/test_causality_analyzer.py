import unittest
import z3

import causality_analyzer
from causality_analyzer import is_candidate_inference, is_candidate_unique_inference

class CausalityAnalyzerTestCase(unittest.TestCase):
    def test_with_booleans(self):
        t = z3.And(True)
        f = z3.And(False)

        assert not is_candidate_inference(t, t, t)
        assert not is_candidate_inference(t, t, f)
        assert not is_candidate_inference(t, f, t)
        assert not is_candidate_inference(t, f, f)
        assert not is_candidate_inference(f, t, t)
        assert not is_candidate_inference(f, t, t)
        assert not is_candidate_inference(f, f, t)
        assert not is_candidate_inference(f, f, f)


    def test_with_two_hypotheses(self):
        t = z3.And(True)
        f = z3.And(False)
        a = z3.Int('a')
        p = (a * a == 4)
        r = (a == -2)
        s = (a == 2)

        assert causality_analyzer.explains_statement(t, p, r)
        assert is_candidate_inference(t, p, r)
        assert is_candidate_inference(t, p, s)


    def test_with_two_hypotheses_extra(self):
        t = z3.And(True)
        f = z3.And(False)
        a = z3.Int('a')
        p = (a * a == 4)
        r = (a == -2)
        s = (a == 2)

        assert causality_analyzer.isnt_straight_up_false(t, p, r)
        assert causality_analyzer.isnt_vacuously_true(t, p, r)
        assert not is_candidate_inference(t, p, p)
        assert not is_candidate_inference(t, p, t)
        assert not is_candidate_inference(t, p, f)
        assert not is_candidate_unique_inference(t, p, r)
        assert not is_candidate_unique_inference(t, p, s)

    def test_valid_demorgan(self):
        a = z3.Bool('a')
        b = z3.Bool('b')
        self.assertTrue(causality_analyzer.check_valid(
            z3.And(a, b) == z3.Not(z3.Or(z3.Not(a), z3.Not(b)))
        ))

    def test_valid_true(self):
        self.assertTrue(causality_analyzer.check_valid(
            z3.And(True)
        ))

    def test_invalid_true(self):
        self.assertFalse(causality_analyzer.check_valid(
            z3.And(False)
        ))
