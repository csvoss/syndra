from datatypes import *
from predicate import *
from structure import *

if __name__ == '__main__':
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

    print predicate.check_sat()
    print predicate.get_model()

    predicate2 = And(
        ModelHasRule(lambda r: And(
                PregraphHas(r, RAF.bound(HRAS.labeled(gtp))),
                PregraphHas(r, MEK1),
                PostgraphHas(r, MEK1.labeled(phosphate))
        )),
        Not(
            ModelHasRule(lambda r: And(
                    PregraphHas(r, RAF.bound(HRAS.labeled(gtp))),
                    PregraphHas(r, MEK1),
                    PostgraphHas(r, MEK1.labeled(phosphate))
            ))
        ))

    print predicate2.check_sat()
    print predicate2.get_model()
