import z3

from structure import *
from predicate import *

phosphate = Label("phosphate")
active = Label("active")

def directly_phosphorylates(kinase, substrate):
    """
    Macro for 'activated "kinase" phosphorylates "substrate"'.

    Arguments:
        kinase: an instance of Structure
        substrate: an instance of Structure

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
        agent: an instance of Structure
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
def directly_activates(name_a, name_b):
    """
    Macro for 'activated "A" activates "B"'.
    """
    pass # TODO: port to new_engine conventions


def negative_residue_behaves_as_if_phosphorylated():
    # For every rule with a phosphate label on site S of protein, there exists a
    # rule doing the same thing which applies to the protein with site S mutated
    # to have a negative amino acid residue.
    # (Whether or not any mutant protein is present at the start of the system
    # is a separate concern, irrelevant to this question.)
    pass

# Then I should be able to assert that if the above global rule is true, then
# phosphorylated A binds B => mutated-A binds B.
def binds(name_a, name_b):
    """Rule for 'A binds B'."""
    pass # TODO: port to new_engine conventions


# Other things: more specific phosphorylation (serine-phosphorylated;
# serine-phosphorylated-at). Can prove theorems about this.

# Other theorems to prove: can't have phosphorylated_is_active and not
# phosphorylated_is_active.

# Use cases for reductions (from transitive closure to minimal set of rules)
# Use cases for inconsistency of rules with each other
# Link to INDRA statements
