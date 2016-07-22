import unittest

from predicate import *
from structure import *
from solver import MySolver

class WaltersExampleTestCase(unittest.TestCase):

    def test_build_context(self):
        raise ValueError()
        RAF = Agent("RAF")
        HRAS = Agent("HRAS")
        MEK1 = Agent("MEK1")
        ERK1 = Agent("ERK1")
        SAF1 = Agent("SAF1")
        gtp = Label("GTP")
        phosphate = Label("phosphate")

        predicate = And(
            ModelHasRule(lambda r: And(
                    PregraphHas(r, RAF.bound(HRAS.labeled(gtp))),
                    PregraphHas(r, MEK1),
                    PostgraphHas(r, MEK1.labeled(phosphate))
            )),
            ModelHasRule(lambda r: And(
                    PregraphHas(r, MEK1.labeled(phosphate)),
                    PregraphHas(r, ERK1),
                    PostgraphHas(r, ERK1.labeled(phosphate))
            )),
            ModelHasRule(lambda r: And(
                    PregraphHas(r, ERK1.labeled(phosphate)),
                    PregraphHas(r, SAF1),
                    PostgraphHas(r, SAF1.labeled(phosphate))
            ))
        )
        solver = MySolver("RAF", "HRAS", "MEK1", "ERK1", "SAF1")
        solver.add(predicate)
        self.assertTrue(solver.check())
        self.assertIsNotNone(solver.model())


    def test_some_unsat_thing(self):
        raise ValueError()
        RAF = Agent("RAF")
        HRAS = Agent("HRAS")
        MEK1 = Agent("MEK1")
        gtp = Label("GTP")
        phosphate = Label("phosphate")

        predicate2 = And(
            ModelHasRule(lambda r: And(
                    PregraphHas(r, RAF.bound(HRAS.labeled(gtp))),
                    PregraphHas(r, MEK1),
                    PostgraphHas(r, MEK1.labeled(phosphate))
            )),
            Not(ModelHasRule(lambda r: And(
                    PregraphHas(r, RAF.bound(HRAS.labeled(gtp))),
                    PregraphHas(r, MEK1),
                    PostgraphHas(r, MEK1.labeled(phosphate))
            )))
        )
        solver = MySolver("RAF", "HRAS", "MEK1")
        solver.add(predicate)
        self.assertFalse(solver.check())
        with self.assertRaises(ValueError):
            solver.model()
