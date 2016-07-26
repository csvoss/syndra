from unittest import TestCase
import datatypes
import predicate

class SimpleSatPredicateTestCase(TestCase):

    def assertSat(self, pred):
        self.assertTrue(pred.check_sat())

    def assertUnsat(self, pred):
        self.assertFalse(pred.check_sat())

    def test_top_sat(self):
        self.assertSat(predicate.Top())

    def test_bottom_unsat(self):
        self.assertUnsat(predicate.Bottom())

    def test_add_sat(self):
        v = datatypes.new_variable()
        pred = predicate.Add(v)
        import pdb; pdb.set_trace()
        self.assertSat(pred)

    def test_rem_sat(self):
        v = datatypes.new_variable()
        pred = predicate.Add(v)
        import pdb; pdb.set_trace()
        self.assertSat(pred)

    def test_equal_sat(self):
        v1 = datatypes.new_variable()
        v2 = datatypes.new_variable()
        pred = predicate.Equal(v1, v2)
        self.assertSat(pred)

    def test_named_sat(self):
        v = datatypes.new_variable()
        s = "Name"
        pred = predicate.Named(v, s)
        self.assertSat(pred)

    def test_prehas_sat(self):
        v = datatypes.new_variable()
        pred = predicate.PreHas(v)
        self.assertSat(pred)

    def test_posthas_sat(self):
        v = datatypes.new_variable()
        pred = predicate.PostHas(v)
        self.assertSat(pred)

    def test_dounlink_sat(self):
        x, y = datatypes.new_variable(), datatypes.new_variable()
        pred = predicate.DoUnlink(x, y)
        self.assertSat(pred)

    def test_dolink_sat(self):
        x, y = datatypes.new_variable(), datatypes.new_variable()
        pred = predicate.DoLink(x, y)
        self.assertSat(pred)

    def test_doparent_sat(self):
        x, y = datatypes.new_variable(), datatypes.new_variable()
        pred = predicate.DoParent(x, y)
        self.assertSat(pred)

    def test_prelabeled_sat(self):
        x = datatypes.new_variable()
        y = "Label"
        pred = predicate.PreLabeled(x, y)
        self.assertSat(pred)

    def test_postlabeled_sat(self):
        x = datatypes.new_variable()
        y = "Label"
        pred = predicate.PostLabeled(x, y)
        self.assertSat(pred)

    def test_preunlabeled_sat(self):
        x = datatypes.new_variable()
        y = "Label"
        pred = predicate.PreUnlabeled(x, y)
        self.assertSat(pred)

    def test_postunlabeled_sat(self):
        x = datatypes.new_variable()
        y = "Label"
        pred = predicate.PostUnlabeled(x, y)
        self.assertSat(pred)

    def test_preparent_sat(self):
        x, y = datatypes.new_variable(), datatypes.new_variable()
        pred = predicate.PreParent(x, y)
        self.assertSat(pred)

    def test_postparent_sat(self):
        x, y = datatypes.new_variable(), datatypes.new_variable()
        pred = predicate.PostParent(x, y)
        self.assertSat(pred)

    def test_prelink_sat(self):
        x, y = datatypes.new_variable(), datatypes.new_variable()
        pred = predicate.PreLink(x, y)
        self.assertSat(pred)

    def test_postlink_sat(self):
        x, y = datatypes.new_variable(), datatypes.new_variable()
        pred = predicate.PostLink(x, y)
        self.assertSat(pred)


class PredicateTestCase(TestCase):

    def setUp(self):
        pass
        # # Some simple predicates for these tests.
        #
        # # This one asserts that some molecule labeled Protein can bind to some
        # # molecule labeled Substrate via some site labeled Site.
        # VarA = datatypes.new_variable("VarA")
        # VarB = datatypes.new_variable("VarB")
        # VarC = datatypes.new_variable("VarC")
        #
        # self.phi = predicate.And(
        #     predicate.PreLabeled(VarA, "Protein"),
        #     predicate.PreLabeled(VarB, "Substrate"),
        #     predicate.PreLabeled(VarC, "Site"),
        #     predicate.PreParent(VarA, VarC),
        #     predicate.DoLink(VarC, VarB) # TODO: ask Adrien why Do and Post both exist
        # )
        #
        # # This one asserts that some molecule labeled D can bind directly to
        # # some molecule labeled E.
        # VarD = datatypes.new_variable("VarD")
        # VarE = datatypes.new_variable("VarE")
        # self.psi = predicate.And(
        #     predicate.PreLabeled(VarD, "D"),
        #     predicate.PreLabeled(VarE, "E"),
        #     predicate.DoLink(VarE, VarD)
        # )
        #
        # self.phi_model = self.phi.get_model()
        # self.psi_model = self.psi.get_model()


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

    # def test_phi_sat(self):
    #     self.assertTrue(self.phi.check_sat())
    #
    #
    # def test_psi_sat(self):
    #     self.assertTrue(self.psi.check_sat())
    #
    #
    # def test_simple_top_model(self):
    #     model = self.top.get_model()
    #
    #     # The model returned should be a set of sets of graph, action pairs.
    #     self.assertIsNotNone(model)
    #     self.assertIsInstance(model, set)
    #
    # # TODO idea: make a library for converting z3 models to more manageable sets
    # # (since you're going to do something similar manually anyways)
    # def test_or(self):
    #     pred = predicate.Or(self.phi, self.psi)
    #
    #     status = pred.check_sat()
    #     # This should be true: such a model can be constructed.
    #     self.assertTrue(status)
    #
    #     # Each of the members of this predicate's model should be equal to
    #     # (s union t), for some s in phi's model and some t in psi's model.
    #
    #     # See the L paper for more details on this; it defines Or in this way.
    #
    #     # NOTE: This implementation assumes the sets are finite. I will have to
    #     # modify this if we decide to support returning some representation of
    #     # infinite models.
    #
    #     def is_union_from_phi_and_psi(graphaction_set):
    #         for s in self.phi_model:
    #             for t in self.psi_model:
    #                 if graphaction_set == s.union(t):
    #                     return True
    #         return False
    #
    #     for graphaction_set in pred.get_model():
    #         self.assertTrue(is_union_from_phi_or_psi(graphaction_set))
    #
    #
    # def test_join(self):
    #     pred = predicate.Join(self.phi, self.psi)
    #
    #     status = pred.check_sat()
    #     # This should be true: such a model can be constructed.
    #     self.assertTrue(status)
    #
    #     # Each of the members of this predicate's model should be equal to
    #     # (s |><| t), for some s in phi's model and some t in psi's model.
    #     # |><| is the lesser join operator:
    #     #       s |><| t =  { <g, a + b> | <g, a> in s, <g, b> in t }.
    #
    #     # Some types for reference:
    #     # |><| :: Set(Graph, Action) -> Set(Graph, Action) -> Set(Graph, Action)
    #     # [[ phi & psi ]] := [[ phi ]] x_|><| [[ psi ]]
    #     #                    :: Set(Set(Graph, Action))
    #
    #     # Again for this, and for the below as well, I'm using the definition
    #     # of the join operator as given in the L paper in order to check
    #     # that my implementation is accurate.
    #
    #     def lesser_join(s, t):
    #         output = set()
    #         for (g1, a1) in s:
    #             for (g2, a2) in t:
    #                 if g1 == g2:
    #                     output.add((g1, a1.union(a2)))
    #         return output
    #
    #     def is_join_from_phi_and_psi(graphaction_set):
    #         for s in self.phi_model:
    #             for t in self.psi_model:
    #                 if lesser_join(s, t) == graphaction_set:
    #                     return True
    #         return False
    #
    #     for graphaction_set in pred.get_model():
    #         self.assertTrue(is_join_from_phi_or_psi(graphaction_set))
    #
    #
    # def test_and(self):
    #     pred = predicate.And(self.phi, self.psi)
    #
    #     status = pred.check_sat()
    #     # This should be true: such a model can be constructed.
    #     self.assertTrue(status)
    #
    #     # Each of the members of this predicate's model should be equal to
    #     # (s intersect t), for some s in phi's model and some t in psi's model.
    #
    #     def is_intersect_from_phi_and_psi(graphaction_set):
    #         for s in self.phi_model:
    #             for t in self.psi_model:
    #                 if graphaction_set == s.intersection(t):
    #                     return True
    #         return False
    #
    #     for graphaction_set in pred.get_model():
    #         self.assertTrue(is_intersect_from_phi_and_psi(graphaction_set))
    #
    #
    # def test_dontknow(self):
    #     pred = predicate.DontKnow(self.phi, self.psi)
    #
    #     status = pred.check_sat()
    #     # This should be true: such a model can be constructed.
    #     self.assertTrue(status)
    #
    #     # This set should be equal to [[phi]] union [[psi]], directly.
    #     self.assertEquals(
    #         pred.get_model(),
    #         self.phi_model.union(self.psi_model)
    #     )
    #
    #
    # def test_not(self):
    #     pred = predicate.Not(self.phi)
    #
    #     status = pred.check_sat()
    #     # This should be true: such a model can be constructed.
    #     pred = predicate.Not(self.phi)
    #
    #     # Again, the whole finite-versus-infinite sets thing makes this tricky.
    #     # I really don't want to be passing around infinite sets for infinite
    #     # models; I'd probably like to reduce those down to a set of minimal
    #     # models, anyways. TBD: how correct this is.
    #
    #     # So, if I'm allowing the model output by [[predicate]] to be something
    #     # minimized, then [[not predicate]] may also be minimized.
    #
    #     # I will assert that everything in [[predicate]] is not in [[not
    #     # predicate]], and that everything in [[not predicate]] is not in
    #     # [[predicate]].
    #
    #     model = pred.get_model()
    #     for graphaction_set in self.phi_model:
    #         assert graphaction_set not in model
    #
    #     for graphaction_set in model:
    #         assert graphaction_set not in self.phi_model
