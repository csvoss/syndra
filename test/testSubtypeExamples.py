import cPickle
import unittest

from metakappa.NodeType import *
from indra_processor.ProcessStatements import *

serine = Residue("Serine")
tyrosine = Residue("Tyrosine")

MEK = ProteinFamily("MEK")
MAP2K1 = Protein("MAP2K1", ["MEK"])
MAP2K2 = Protein("MAP2K2", ["MEK"])

RAF = ProteinFamily("RAF")
RAF1_BRAF = ProteinFamily("RAF1_BRAF")

RAF1 = Protein("RAF1", ["RAF", "RAF1_BRAF"])
ARAF = Protein("ARAF", ["RAF"])
BRAF = Protein("BRAF", ["RAF"])

S222 = Site("S222", "Serine")

class TestNodeType(unittest.TestCase):
    def setUp(self):
        pass

    def openFile(self, filename):
        with open(filename, "r") as f:
            return cPickle.load(f)

    def test_example_1(self):
        """
        Reads two statements, one where BRAF is phosphorylated and one where RAF
        is phosphorylated. Returns that we can have one or the other, but not both.
        """
        example = self.openFile("examples/syndra_example_1.pkl")
        processStatements(example.statements)
        self.assertTrue(False)

    def test_residues(self):
        self.assertFalse(infamily(serine, S222))
        self.assertTrue(infamily(serine, Agent()))

    def test_proteinFamilies(self):
        self.assertTrue(infamily(MAP2K1, MEK))
        self.assertFalse(infamily(MAP2K1, RAF))
        self.assertTrue(infamily(MAP2K1, Agent()))
        self.assertTrue(infamily(RAF1, RAF))
        self.assertTrue(infamily(RAF1, RAF1_BRAF))
        self.assertFalse(infamily(RAF1, MEK))
        self.assertFalse(infamily(RAF1, RAF1))
        self.assertFalse(infamily(RAF1, ARAF))
