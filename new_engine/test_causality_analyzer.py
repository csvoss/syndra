import unittest
import z3

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

        assert is_candidate_inference(t, p, r)
        assert is_candidate_inference(t, p, s)
        assert not is_candidate_inference(t, p, p)
        assert not is_candidate_inference(t, p, t)
        assert not is_candidate_inference(t, p, f)
        assert not is_candidate_unique_inference(t, p, r)
        assert not is_candidate_unique_inference(t, p, s)
