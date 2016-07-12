import unittest

from datatypes import *
from predicate import *
from structure import *

class WaltersExampleTestCase(unittest.TestCase):

    def test_build_context(self):
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
        self.assertTrue(predicate.check_sat())
        self.assertIsNotNone(predicate.get_model())


    def test_some_unsat_thing(self):
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
        self.assertFalse(predicate2.check_sat())
        with self.assertRaises(ValueError):
            predicate2.get_model()
