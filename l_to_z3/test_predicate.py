from unittest import TestCase
import model
import predicate
import z3

class PredicateTestCase(TestCase):

    def setUp(self):
        m = model.Model()
        self.top = predicate.Top(m)

    def test_simple_instantiation(self):
        pass

    def test_simple_check_sat(self):
        status = self.top.check_sat()
        self.assertEquals(status, z3.sat)

    def test_simple_get_model(self):
        model = self.top.get_model()
        self.assertIsNotNone(model)

    def test_simple_get_all_models(self):
        models = self.top.get_models()
        self.assertNotEqual(len(models), 0)
