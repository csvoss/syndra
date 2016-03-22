import atomic_predicate
import datatypes
from datatypes import new_variable
import predicate
import z3

from labels import ACTIVE, PHOSPHORYLATED

def directly_phosphorylates(name_a, name_b):
    """
    Macro for '"A" phosphorylates "B"'.
    """
    A = new_variable(nickname=name_a)
    B = new_variable(nickname=name_b)

    # Okay, so what I actually want this to say is as follows:
    # Forall Model, Exists Rule in Model, reaction stuff holds over rule
    # reaction stuff = Forall A B, Named A name_a /\ Named B name_b => prelabeled etc
    intp = datatypes.new_interpretation()

    # Manual implementation
    return predicate.Exists(predicate.Implies(predicate.Named(A, name_a),
            predicate.Implies(predicate.Named(B, name_b),
                predicate.And(predicate.PreLabeled(A, ACTIVE),
                    predicate.PreUnlabeled(B, PHOSPHORYLATED),
                    predicate.PostLabeled(A, ACTIVE),
                    predicate.PostLabeled(B, PHOSPHORYLATED)))))


# n.b.: there is an INDRA statement for this -- posttranslational modification
def phosphorylated_is_active(name_b):
    """
    Macro for 'phosphorylated "B" is active'.
    """
    # Forall Model, *Forall* Rule in Model, Forall B, Named B named_b => and(...)
    B = new_variable(nickname=name_b)

    intp = datatypes.new_interpretation()

    # Manual implementation
    return predicate.ForAll(predicate.Implies(predicate.Named(B, name_b),
        predicate.And(predicate.Implies(predicate.PreLabeled(B, PHOSPHORYLATED),
                    predicate.PreLabeled(B, ACTIVE)),
            predicate.Implies(predicate.PostLabeled(B, PHOSPHORYLATED),
                    predicate.PostLabeled(B, ACTIVE)))))


# n.b.: this is ActivityActivity
def directly_activates(name_a, name_b):
    """
    Macro for '"A" activates "B"'.
    """
    # Forall Model, Exists Rule in Model, [...]
    A = new_variable(nickname=name_a)
    B = new_variable(nickname=name_b)

    intp = datatypes.new_interpretation()

    return predicate.Exists(predicate.Implies(predicate.Named(A, name_a),
            predicate.Implies(predicate.Named(B, name_b),
                predicate.And(predicate.PreLabeled(A, ACTIVE),
                    predicate.PreUnlabeled(B, ACTIVE),
                    predicate.PostLabeled(A, ACTIVE),
                    predicate.PostLabeled(B, ACTIVE)))))


# Other things: more specific phosphorylation (serine-phosphorylated;
# serine-phosphorylated-at). Can prove theorems about this.

# Other theorems to prove: can't have phosphorylated_is_active and not
# phosphorylated_is_active.

# Use cases for reductions (from transitive closure to minimal set of rules)
# Use cases for inconsistency of rules with each other
# Link to INDRA statements
