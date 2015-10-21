"""Testing simple inferences

.. moduleauthor:: Jean Yang <jean_yang@hms.harvard.edu>
"""
from z3 import *

# Sites.
Site = DeclareSort('Site')
MEK = Const('MEK', Site)

# Activities.
active = Function('active', Site, BoolSort())
kinase_active = Function('kinase_active', Site, BoolSort())

# More on kinases.
KinaseFamily = DeclareSort('KinaseFamily')
Serine = Const('Serine', KinaseFamily)
KinaseMolecule = DeclareSort('KinaseMolecule')
S222 = Const('S222', KinaseMolecule)
KinaseLabel = Datatype('KinaseLabel')
KinaseLabel.declare('none')
KinaseLabel.declare('family', ('f', KinaseFamily))
KinaseLabel.declare('kinase', ('k', KinaseMolecule))
KinaseLabel = KinaseLabel.create()

kinase_subsumes = Function('kinase_subsumes'
    , KinaseLabel, KinaseLabel, BoolSort())
in_kinase_family = Function('in_kinase_family'
    , KinaseLabel, KinaseLabel, BoolSort())
phosphorylated = Function('phosphorylated'
    , Site, KinaseLabel, BoolSort())

s = Const('s', Site)
k1 = Const('k1', KinaseLabel)
k2 = Const('k2', KinaseLabel)
inferenceRules = [
    ForAll(s, Implies(kinase_active(s), active(s)))
    # Subsumption relationship based on "family" relationship.
    , ForAll(k1
        , ForAll(k2
            , Implies(in_kinase_family(k1, k2), kinase_subsumes(k2, k1))))
    # Having some information subsumes having no information.
    , ForAll(k1, kinase_subsumes(k1, KinaseLabel.none))
    # If we know something more specific phosphorylates a site, then we can
    # infer the more general phosphorylation.
    , ForAll(s
        ,   ForAll(k1
            , ForAll(k2
                , Implies(And(kinase_subsumes(k2, k1), phosphorylated(s, k2))
                    , phosphorylated(s, k1)))))
]

class SimpleInferenceEngine:
    def __init__(self):
        self.solver = z3.Solver()

        for constraint in inferenceRules:
            self.solver.add(constraint)

    def z3_assert(self, constraint):
        self.solver.add(constraint)

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def check(self, constraint):
        self.solver.push()
        self.solver.add(constraint)
        print self.solver.check()
        self.solver.pop()

def testActivity(engine):
    engine.push()
    s1 = Const('s1', Site)
    engine.z3_assert(kinase_active(s1))

    # Should be unsat.
    engine.check(Not(active(s1)))
    engine.pop()

def testPhosphorylation(engine):
    serine = KinaseLabel.family(Serine)
    s222 = KinaseLabel.kinase(S222)

    engine.push()
    engine.z3_assert(in_kinase_family(serine, s222))
    engine.z3_assert(phosphorylated(MEK, s222))
    engine.z3_assert(kinase_subsumes(s222, serine))

    # Sanity checks.
    engine.check(kinase_subsumes(s222, KinaseLabel.none))
    engine.check(phosphorylated(MEK, serine))
    engine.check(phosphorylated(MEK, KinaseLabel.none))

    # This should be unsat.
    engine.check(Not(phosphorylated(MEK, serine)))
    engine.check(Not(phosphorylated(MEK, KinaseLabel.none)))
    engine.pop()

if __name__ == "__main__":
    engine = SimpleInferenceEngine()
    testActivity(engine)
    testPhosphorylation(engine)
