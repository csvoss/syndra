"""Data types for nodes in the graph.

.. moduleauthor:: Jean Yang <jean_yang@hms.harvard.edu>
"""
class Agent(object):
    def __init__(self):
        self.parents = []
        self.name = ""
    def __eq__(self, other):
        return self.name == other.name and self.parents == other.parents

class ProteinFamily(Agent):
    def __init__(self, name):
        super(ProteinFamily, self).__init__()
        self.name = name

class Protein(ProteinFamily):
    def __init__(self, name, parents):
        for parent in parents:
            super(Protein, self).__init__(parent)
        self.name = name
        self.parents.extend(parents)

class Residue(Agent):
    """A residue is an amino acid monomer.
    """
    def __init__(self, name):
        super(Residue, self).__init__()
        self.name = name

class Site(Residue):
    """A site is a region on a protein to which ligands may form a bond.
       Note that we can't strictly use subtyping relationships because sites
       are both in the "Residue" family and a specific protein family.
    """
    def __init__(self, name, parent):
        super(Site, self).__init__(parent)
        self.name = name
        self.parents.append(parent) # Note that this has to be an amino acid.

def canmerge(name, parents):
    return name=="" or name in parents

def infamily(v, parent):
    """Returns whether the value 'v' is in the family of 'parent.'
       The idea is to use this function to decide when we can combine
       actions we get from the NLP.
    """
    return issubclass(v.__class__, parent.__class__) and \
        canmerge(parent.name, v.parents)
