import unittest

from metakappa.NodeType import *

serine = Residue("Serine")
tyrosine = Residue("Tyrosine")

MEK = ProteinFamily("MEK")
MAP2K1 = Protein("MAP2K1", ["MEK"])
MAP2K2 = Protein("MAP2K2", ["MEK"])

Raf = ProteinFamily("Raf")
RAF1_BRAF = ProteinFamily("RAF1_BRAF")

RAF1 = Protein("RAF1", ["Raf", "RAF1_BRAF"])
ARAF = Protein("ARAF", ["Raf"])

S222 = Site("S222", "Serine")

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
