import unittest

from metakappa.DomainFacts import *

class TestNodeType(unittest.TestCase):
    def setUp(self):
        pass

    def test_sites(self):
        self.assertTrue(infamily(S222, serine))
        self.assertFalse(infamily(S222, tyrosine))
        self.assertTrue(infamily(S222, Agent()))

    def test_residues(self):
        self.assertFalse(infamily(serine, S222))
        self.assertTrue(infamily(serine, Agent()))

    def test_proteinFamilies(self):
        self.assertTrue(infamily(MAP2K1, MEK))
        self.assertFalse(infamily(MAP2K1, Raf))
        self.assertTrue(infamily(MAP2K1, Agent()))
        self.assertTrue(infamily(RAF1, Raf))
        self.assertTrue(infamily(RAF1, RAF1_BRAF))
        self.assertFalse(infamily(RAF1, MEK))
        self.assertFalse(infamily(RAF1, RAF1))
        self.assertFalse(infamily(RAF1, ARAF))
