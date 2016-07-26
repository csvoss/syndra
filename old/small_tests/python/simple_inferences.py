"""Testing simple inferences

.. moduleauthor:: Jean Yang <jean_yang@hms.harvard.edu>
"""
from z3 import *

# Proteins.
Protein = DeclareSort('Protein')
MEK = Const('MEK', Protein)

# Activities.
active = Function('active', Protein, BoolSort())
kinase_active = Function('kinase_active', Protein, BoolSort())

# More on proteins and sites.
Residue = DeclareSort('Residue')
Serine = Const('Serine', Residue)
Site = DeclareSort('Site')
S222 = Const('S222', Site)
SiteLabel = Datatype('SiteLabel')
SiteLabel.declare('none')
SiteLabel.declare('residue', ('f', Residue))
SiteLabel.declare('site', ('k', Site))
SiteLabel = SiteLabel.create()

site_refines = Function('site_refines'
    , SiteLabel, SiteLabel, BoolSort())
in_family = Function('in_family'
    , SiteLabel, SiteLabel, BoolSort())
phosphorylated = Function('phosphorylated'
    , Protein, SiteLabel, BoolSort())

s = Const('s', Protein)
k1 = Const('k1', SiteLabel)
k2 = Const('k2', SiteLabel)
inferenceRules = [
    ForAll(s, Implies(kinase_active(s), active(s)))
    # Subsumption relationship based on "family" relationship.
    , ForAll(k1
        , ForAll(k2
            , Implies(in_family(k1, k2), site_refines(k2, k1))))
    # Having some information subsumes having no information.
    , ForAll(k1, site_refines(k1, SiteLabel.none))
    # If we know something more specific phosphorylates a site, then we can
    # infer the more general phosphorylation.
    , ForAll(s
        ,   ForAll(k1
            , ForAll(k2
                , Implies(And(site_refines(k2, k1), phosphorylated(s, k2))
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
    s1 = Const('s1', Protein)
    engine.z3_assert(kinase_active(s1))

    # Should be unsat.
    engine.check(Not(active(s1)))
    engine.pop()

def testPhosphorylation(engine):
    serine = SiteLabel.residue(Serine)
    s222 = SiteLabel.site(S222)

    engine.push()
    engine.z3_assert(in_family(serine, s222))
    engine.z3_assert(phosphorylated(MEK, s222))
    engine.z3_assert(site_refines(s222, serine))

    # Sanity checks.
    engine.check(site_refines(s222, SiteLabel.none))
    engine.check(phosphorylated(MEK, serine))
    engine.check(phosphorylated(MEK, SiteLabel.none))

    # This should be unsat.
    engine.check(Not(phosphorylated(MEK, serine)))
    engine.check(Not(phosphorylated(MEK, SiteLabel.none)))
    engine.pop()

if __name__ == "__main__":
    engine = SimpleInferenceEngine()
    testActivity(engine)
    testPhosphorylation(engine)
