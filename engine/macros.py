"""
This module stores macros: a collection of Syndra predicates for representing
standard concepts like phosphorylation and activation.
"""

from structure import Label
from predicate import PregraphHas, ModelHasRule, Not, PostgraphHas, Implies, ForAllRules, And

phosphate = Label("phosphate")
active = Label("active")

def directly_phosphorylates(kinase, substrate):
    """
    Macro for 'activated "kinase" phosphorylates "substrate"'.

    Arguments:
        kinase: an instance of structure.Structure
        substrate: an instance of structure.Structure

    Returns:
        a Syndra predicate (that is, an instance of predicate.Predicate)
    """
    return ModelHasRule(lambda r: And(
        PregraphHas(r, kinase.labeled(active)),
        PregraphHas(r, substrate),
        PostgraphHas(r, kinase.labeled(active)),
        PostgraphHas(r, substrate.labeled(phosphate)),
        Not(PregraphHas(r, substrate.labeled(phosphate))),
    ))

# n.b.: there is an INDRA statement for this -- posttranslational modification
def phosphorylated_is_active(agent):
    """
    Macro for 'phosphorylated "B" is active'.

    Arguments:
        agent: an instance of structure.Structure

    Returns:
        a Syndra predicate (that is, an instance of predicate.Predicate)
    """
    return ForAllRules(lambda r:
                       And(
                           Implies(
                               PregraphHas(r, agent.labeled(phosphate)),
                               PregraphHas(r, agent.labeled(active))
                           ),
                           Implies(
                               PostgraphHas(r, agent.labeled(phosphate)),
                               PostgraphHas(r, agent.labeled(active))
                           )))



# n.b.: this is Activation
def directly_activates(kinase, substrate):
    """
    Macro for 'activated "kinase" activates "substrate"'.

    Arguments:
        kinase: an instance of structure.Structure
        substrate: an instance of structure.Structure

    Returns:
        a Syndra predicate (that is, an instance of predicate.Predicate)
    """
    return ModelHasRule(lambda r: And(
        PregraphHas(r, kinase.labeled(active)),
        PregraphHas(r, substrate),
        PostgraphHas(r, kinase.labeled(active)),
        PostgraphHas(r, substrate.labeled(active)),
        Not(PregraphHas(r, substrate.labeled(active))),
    ))


# More ideas for macros below; unimplemented.

# For every rule with a phosphate label on site S of protein, there exists a
# rule doing the same thing which applies to the protein with site S mutated
# to have a negative amino acid residue.
# (Whether or not any mutant protein is present at the start of the system
# is a separate concern, irrelevant to this question.)

# Then I should be able to assert that if the above global rule is true, then
# phosphorylated A binds B => mutated-A binds B.

# Other things: more specific phosphorylation (serine-phosphorylated;
# serine-phosphorylated-at). Can prove theorems about this.

# Other theorems to prove: can't have phosphorylated_is_active and not
# phosphorylated_is_active.

# Use cases for reductions (from transitive closure to minimal set of rules)
# Use cases for inconsistency of rules with each other
# Link to INDRA statements
