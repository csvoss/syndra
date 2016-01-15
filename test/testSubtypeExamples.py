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
        Reads two statements, one where BRAF is phosphorylated and one where RAF
        is phosphorylated. Returns that we can have one or the other, but not
        both.
        """
        example = self.openFile("examples/syndra_example_1.pkl")
        clusters = processStatements(example.statements)
        print clusters
        self.assertEqual(len(clusters), 1)
        self.assertEqual(len(clusters[0]), 2)

    def test_example_2(self):
        """
        Reads three statements, with BRAF, ARAF, and RAF. Groups them into the
        same cluster.

        Advanced: Determines we should be able to have only RAF?
        """
        example = self.openFile("examples/syndra_example_2.pkl")
        clusters = processStatements(example.statements)
        print clusters
        self.assertEqual(len(clusters), 1)
        self.assertEqual(len(clusters[0]), 3)
        # TODO: The advanced stuff

    def test_example_3(self):
        """
        This example involves unifying not just proteins in the same family,
        but different levels of knowledge involving phosphorylation.
        """
        # TODO: Implement combining Phosphorylation with SerinePhos.
        example = self.openFile("examples/syndra_example_3.pkl")
        clusters = processStatements(example.statements)
        # print clusters
        self.assertEqual(len(clusters), 1)

    def test_example_4(self):
        """
        This is the really big example.
        """
        example = self.openFile("examples/syndra_example_4.pkl")
