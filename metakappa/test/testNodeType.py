from NodeType import *
import unittest

class TestNodeType(unittest.TestCase):
    def setUp(self):
        self.MEK = Protein()
        self.S222 = Site(Serine) # Pass the Serine type as an argument for the
                                 # residue it's associated with.

    def test_subtype(self):
        self.assertTrue(isSubtype(self.S222, Serine))
        self.assertFalse(isSubtype(self.S222, Tyrosine))
