import cPickle
import unittest

from metakappa.DomainFacts import *
from indra_processor.ProcessStatements import *

class TestSubtypeExamples(unittest.TestCase):
    def setUp(self):
        pass

    def openFile(self, filename):
        with open(filename, "r") as f:
            return cPickle.load(f)

    def test_example_1(self):
        """
        Reads two statements, one where BRAF is phosphorylated and one where RAF        is phosphorylated. Returns that we can have one or the other, but not
        both.
        """
        example = self.openFile("examples/syndra_example_1.pkl")
        clusters = processStatements(example.statements)
        print clusters
        self.assertEqual(len(clusters), 1)
        self.assertEqual(len(clusters[0]), 2)
