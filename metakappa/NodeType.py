"""Data types for nodes in the graph.

.. moduleauthor:: Jean Yang <jean_yang@hms.harvard.edu>
"""
class Agent:
    pass

class Protein(Agent):
    pass

class Residue(Agent):
    """A residue is an amino acid monomer.
    """
    pass
class Serine(Residue):
    pass
class Tyrosine(Residue):
    pass

class Site(Residue):
    """A site is a region on a protein to which ligands may form a bond.
       Note that we can't strictly use subtyping relationships because sites
       are both in the "Residue" family and a specific protein family.
    """
    def __init__(self, residue):
        self.residue = residue # Note that this has to be an amino acid.
    def __eq__(self, other):
        self.residue == other.residue

def isSubtype(v, parent):
    """Returns whether the value 'v' is in the family of 'parent.'
       TODO: Generalize this function once we have more types.
    """
    if isinstance(v, Site):
        # If we have a site, need to additionally check that v's parent residue
        # is the same as the parent residue.
        if issubclass(parent, Site):
            return v==parent
        elif issubclass(parent, Residue):
            print v.residue
            return v.residue==parent
        else:
            return issubclass(v.__class__, parent)
    else:
        return issubclass(v.__class__, parent)
