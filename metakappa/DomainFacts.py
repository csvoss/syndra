from NodeType import *

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

# TODO: Activity levels.

typeMappings = {
    "Serine" : serine
    , "Tyrosine" : tyrosine
    , "MEK" : MEK
    , "MAP2K1" : MAP2K1
    , "MAP2K2" : MAP2K2
    , "RAF" : RAF
    , "RAF1_BRAF" : RAF1_BRAF
    , "RAF1" : RAF1
    , "ARAF" : ARAF
    , "BRAF" : BRAF
}
