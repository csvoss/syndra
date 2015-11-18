from Model import *
import unittest

class TestModel(unittest.TestCase):
    def setUp(self):
        self.model = Model()

    def test_init_action_graph_id(self):
        a = Action(GraphId())
        self.assertEqual(a.ag_add, Set())

    def test_init_action_ag_add(self):
        pass

    def test_apply_action(self):
        # Test noop.

        # Test add agent.

        # Test remove agent.
        pass
