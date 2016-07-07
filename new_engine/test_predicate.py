import unittest

import predicate
import datatypes
import structure

class SimplePredicateTestCase(unittest.TestCase):
    def assertSat(self, pred):
        self.assertTrue(pred.check_sat())

    def assertUnsat(self, pred):
        self.assertFalse(pred.check_sat())

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
        self.phi_model = self.phi.get_model()
        self.psi_model = self.psi.get_model()


    def test_and_sat(self):
        p1 = predicate.Top()
        p2 = predicate.Top()
        status = predicate.And(p1, p2)
        self.assertTrue(status)

    def test_and_unsat(self):
        p1 = predicate.Top()
        p2 = predicate.Bottom()
        status = predicate.And(p1, p2)
        self.assertTrue(status)

    def test_or_sat(self):
        p1 = predicate.Bottom()
        p2 = predicate.Top()
        status = predicate.Or(p1, p2)
        self.assertTrue(status)

    def test_or_unsat(self):
        p1 = predicate.Bottom()
        p2 = predicate.Bottom()
        status = predicate.Or(p1, p2)
        self.assertTrue(status)

    def test_phi_sat(self):
        self.assertTrue(self.phi.check_sat())


    def test_psi_sat(self):
        self.assertTrue(self.psi.check_sat())


@unittest.skip("Uncomment this class when you can convert z3 models to Python sets of rules.")
class ModelsAsSetsTestCase(unittest.TestCase):
    def test_simple_top_model(self):
        model = predicate.Top().get_model()

        # The model returned should be a set of sets of graph, action pairs.
        self.assertIsNotNone(model)
        self.assertIsInstance(model, set)

    # TODO idea: make a library for converting z3 models to more manageable sets
    # (since you're going to do something similar manually anyways)
    def test_or(self):
        pred = predicate.Or(self.phi, self.psi)

        status = pred.check_sat()
        # This should be true: such a model can be constructed.
        self.assertTrue(status)

        # Each of the members of this predicate's model should be equal to
        # (s union t), for some s in phi's model and some t in psi's model.

        # See the L paper for more details on this; it defines Or in this way.

        # NOTE: This implementation assumes the sets are finite. I will have to
        # modify this if we decide to support returning some representation of
        # infinite models.

        def is_union_from_phi_and_psi(graphaction_set):
            for s in self.phi_model:
                for t in self.psi_model:
                    if graphaction_set == s.union(t):
                        return True
            return False

        for graphaction_set in pred.get_model():
            self.assertTrue(is_union_from_phi_or_psi(graphaction_set))


    def test_join(self):
        pred = predicate.Join(self.phi, self.psi)

        status = pred.check_sat()
        # This should be true: such a model can be constructed.
        self.assertTrue(status)

        # Each of the members of this predicate's model should be equal to
        # (s |><| t), for some s in phi's model and some t in psi's model.
        # |><| is the lesser join operator:
        #       s |><| t =  { <g, a + b> | <g, a> in s, <g, b> in t }.

        # Some types for reference:
        # |><| :: Set(Graph, Action) -> Set(Graph, Action) -> Set(Graph, Action)
        # [[ phi & psi ]] := [[ phi ]] x_|><| [[ psi ]]
        #                    :: Set(Set(Graph, Action))

        # Again for this, and for the below as well, I'm using the definition
        # of the join operator as given in the L paper in order to check
        # that my implementation is accurate.

        def lesser_join(s, t):
            output = set()
            for (g1, a1) in s:
                for (g2, a2) in t:
                    if g1 == g2:
                        output.add((g1, a1.union(a2)))
            return output

        def is_join_from_phi_and_psi(graphaction_set):
            for s in self.phi_model:
                for t in self.psi_model:
                    if lesser_join(s, t) == graphaction_set:
                        return True
            return False

        for graphaction_set in pred.get_model():
            self.assertTrue(is_join_from_phi_or_psi(graphaction_set))


    def test_and(self):
        pred = predicate.And(self.phi, self.psi)

        status = pred.check_sat()
        # This should be true: such a model can be constructed.
        self.assertTrue(status)

        # Each of the members of this predicate's model should be equal to
        # (s intersect t), for some s in phi's model and some t in psi's model.

        def is_intersect_from_phi_and_psi(graphaction_set):
            for s in self.phi_model:
                for t in self.psi_model:
                    if graphaction_set == s.intersection(t):
                        return True
            return False

        for graphaction_set in pred.get_model():
            self.assertTrue(is_intersect_from_phi_and_psi(graphaction_set))


    def test_dontknow(self):
        pred = predicate.DontKnow(self.phi, self.psi)

        status = pred.check_sat()
        # This should be true: such a model can be constructed.
        self.assertTrue(status)

        # This set should be equal to [[phi]] union [[psi]], directly.
        self.assertEquals(
            pred.get_model(),
            self.phi_model.union(self.psi_model)
        )


    def test_not(self):
        pred = predicate.Not(self.phi)

        status = pred.check_sat()
        # This should be true: such a model can be constructed.
        pred = predicate.Not(self.phi)
        model = pred.get_model()

        for rule in self.phi_model:
            assert rule not in model

        for rule in model:
            assert rule not in self.phi_model
