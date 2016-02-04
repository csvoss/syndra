from unittest import TestCase
import model
import z3

# TODO: These test cases are obsolete.

# Can't write more until I fix the "Valid list of accessors expected. An
# accessor is a pair of the form (String, Datatype|Sort)" error I'm seeing
# when I run model.py.

class ModelTestCase(TestCase):

    def test_simple_instantiation(self):
        g = model.Pregraph()
        a = model.Action()
        p = model.Postgraph(g, a)

    def test_model_instantiation(self):
        m = model.Model()

    def test_model_add_assertions(self):
        m = model.Model()
        s = z3.Solver()
        m.add_assertions(s)
