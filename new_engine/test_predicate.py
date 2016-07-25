import unittest

import predicate
import structure

from solver import MySolver
solver = MySolver("enzyme", "enzyme_site", "substrate", "d", "e")

class SimplePredicateTestCase(unittest.TestCase):
    def assertSat(self, pred):
        self.assertTrue(solver.quick_check(pred))

    def assertUnsat(self, pred):
        self.assertFalse(solver.quick_check(pred))

    def test_top_sat(self):
        self.assertSat(predicate.Top())

    def test_bottom_unsat(self):
        self.assertUnsat(predicate.Bottom())

    def test_modelhasrule_sat(self):
        pred = predicate.ModelHasRule(lambda r: predicate.Top())
        self.assertSat(pred)


class PredicateTestCase(unittest.TestCase):
    def setUp(self):
        enzyme = structure.Agent("enzyme")
        enzyme_site = structure.Agent("enzyme_site")
        substrate = structure.Agent("substrate")
        # This one asserts that some molecule labeled Protein can bind to some
        # molecule labeled Substrate via some site labeled Site.
        self.phi = predicate.ModelHasRule(lambda r: predicate.And(
                predicate.PregraphHas(r, enzyme.with_site(enzyme_site)),
                predicate.PregraphHas(r, substrate),
                predicate.PostgraphHas(r, enzyme.with_site(enzyme_site.bound(substrate)))
        ))
        # This one asserts that some molecule labeled D can bind directly to
        # some molecule labeled E.
        d = structure.Agent("d")
        e = structure.Agent("e")
        self.psi = predicate.ModelHasRule(lambda r: predicate.And(
                predicate.PregraphHas(r, d),
                predicate.PregraphHas(r, e),
                predicate.PostgraphHas(r, e.bound(d))
        ))

    def test_and_sat(self):
        p1 = predicate.Top()
        p2 = predicate.Top()
        status = solver.quick_check(predicate.And(p1, p2))
        self.assertTrue(status)

    def test_and_unsat(self):
        p1 = predicate.Top()
        p2 = predicate.Bottom()
        status = solver.quick_check(predicate.And(p1, p2))
        self.assertFalse(status)

    def test_or_sat(self):
        p1 = predicate.Bottom()
        p2 = predicate.Top()
        status = solver.quick_check(predicate.Or(p1, p2))
        self.assertTrue(status)

    def test_or_unsat(self):
        p1 = predicate.Bottom()
        p2 = predicate.Bottom()
        status = solver.quick_check(predicate.Or(p1, p2))
        self.assertFalse(status)

    def test_phi_sat(self):
        self.assertTrue(solver.quick_check(self.phi))

    def test_psi_sat(self):
        self.assertTrue(solver.quick_check(self.psi))
