from unittest import TestCase
import predicate

class PredicateTestCase(TestCase):

    def setUp(self):
        self.top = predicate.Top()
        self.bottom = predicate.Bottom()

        # Some simple predicates for these tests.

        # This one asserts that some molecule labeled A can bind to some
        # molecule labeled B via some site labeled C.
        self.phi = predicate.And(
            predicate.Labeled("VarA", "A"),
            predicate.Labeled("VarB", "B"),
            predicate.Labeled("VarC", "C"),
            predicate.PreParent("VarA", "VarC"),
            predicate.DoLink("VarC", "VarB")
        )

        # This one asserts that some molecule labeled D can bind directly to
        # some molecule labeled B.
        self.psi = predicate.And(
            predicate.Labeled("VarD", "D"),
            predicate.Labeled("VarB", "B"),
            predicate.DoLink("VarB", "VarD")
        )

        self.phi_model = self.phi.get_model()
        self.psi_model = self.psi.get_model()


    def test_top_sat(self):
        self.assertTrue(self.top.check_sat())


    def test_bottom_unsat(self):
        self.assertFalse(self.bottom.check_sat())


    def test_phi_sat(self):
        self.assertTrue(self.phi.check_sat())


    def test_psi_sat(self):
        self.assertTrue(self.psi.check_sat())


    def test_simple_top_model(self):
        model = self.top.get_model()

        # The model returned should be a set of sets of graph, action pairs.
        self.assertIsNotNone(model)
        self.assertIsInstance(model, set)


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

        # Again, the whole finite-versus-infinite sets thing makes this tricky.
        # I really don't want to be passing around infinite sets for infinite
        # models; I'd probably like to reduce those down to a set of minimal
        # models, anyways. TBD: how correct this is.

        # So, if I'm allowing the model output by [[predicate]] to be something
        # minimized, then [[not predicate]] may also be minimized.

        # I will assert that everything in [[predicate]] is not in [[not
        # predicate]], and that everything in [[not predicate]] is not in
        # [[predicate]].

        model = pred.get_model()
        for graphaction_set in self.phi_model:
            assert graphaction_set not in model

        for graphaction_set in model:
            assert graphaction_set not in self.phi_model
