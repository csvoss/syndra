import atomic_predicate
import datatypes
from datatypes import new_variable
import predicate
from predicate import PreLabeled, PreUnlabeled, Named, PostLabeled, And, Implies, ForAll
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

    g = datatypes.new_graph('g')
    a = datatypes.new_action('a')
    intp = datatypes.new_interpretation()
    subm = predicate.model_from(g, a)

    # Manual implementation
    return z3.Exists([g, a], z3.Implies(atomic_predicate.Named(A, name_a)._assert(subm, intp),
            z3.Implies(atomic_predicate.Named(B, name_b)._assert(subm, intp),
                z3.And(atomic_predicate.PreLabeled(A, ACTIVE)._assert(subm, intp),
                    atomic_predicate.PreUnlabeled(B, PHOSPHORYLATED)._assert(subm, intp),
                    atomic_predicate.PostLabeled(A, ACTIVE)._assert(subm, intp),
                    atomic_predicate.PostLabeled(B, PHOSPHORYLATED)._assert(subm, intp)))))

    # Old implementation
    return ForAll(A, ForAll(B,
               Implies(Named(A, name_a), Implies(Named(B, name_b),
                   And(PreLabeled(A, ACTIVE),
                       PreUnlabeled(B, PHOSPHORYLATED),
                       PostLabeled(A, ACTIVE),
                       PostLabeled(B, PHOSPHORYLATED))))))

# n.b.: there is an INDRA statement for this -- posttranslational modification
def phosphorylated_is_active(name_b):
    """
    Macro for 'phosphorylated "B" is active'.
    """
    # Forall Model, *Forall* Rule in Model, Forall B, Named B named_b => and(...)
    B = new_variable(nickname=name_b)

    g = datatypes.new_graph('g')
    a = datatypes.new_action('a')
    intp = datatypes.new_interpretation()
    subm = predicate.model_from(g, a)

    # Manual implementation
    return z3.ForAll([g, a], z3.Implies(atomic_predicate.Named(B, name_b)._assert(subm, intp),
        z3.And(z3.Implies(atomic_predicate.PreLabeled(B, PHOSPHORYLATED)._assert(subm, intp),
                    atomic_predicate.PreLabeled(B, ACTIVE)._assert(subm, intp)),
            z3.Implies(atomic_predicate.PostLabeled(B, PHOSPHORYLATED)._assert(subm, intp),
                    atomic_predicate.PostLabeled(B, ACTIVE)._assert(subm, intp)))))

    # Old
    return ForAll(B, Implies(Named(B, name_b),
               And(Implies(PreLabeled(B, PHOSPHORYLATED),
                           PreLabeled(B, ACTIVE)),
                   Implies(PostLabeled(B, PHOSPHORYLATED),
                           PostLabeled(B, ACTIVE)))))

# n.b.: this is ActivityActivity
def directly_activates(name_a, name_b):
    """
    Macro for '"A" activates "B"'.
    """
    # Forall Model, Exists Rule in Model, [...]
    A = new_variable(nickname=name_a)
    B = new_variable(nickname=name_b)

    g = datatypes.new_graph('g')
    a = datatypes.new_action('a')
    intp = datatypes.new_interpretation()
    subm = predicate.model_from(g, a)

    # Manual implementation
    return z3.Exists([g, a], z3.Implies(atomic_predicate.Named(A, "MEK")._assert(subm, intp),
            z3.Implies(atomic_predicate.Named(B, "ERK")._assert(subm, intp),
                z3.And(atomic_predicate.PreLabeled(A, ACTIVE)._assert(subm, intp),
                    atomic_predicate.PreUnlabeled(B, ACTIVE)._assert(subm, intp),
                    atomic_predicate.PostLabeled(A, ACTIVE)._assert(subm, intp),
                    atomic_predicate.PostLabeled(B, ACTIVE)._assert(subm, intp)))))

    # Old
    return ForAll(A, ForAll(B,
               Implies(Named(A, name_a), Implies(Named(B, name_b),
                   And(PreLabeled(A, ACTIVE),
                       PreUnlabeled(B, ACTIVE),
                       PostLabeled(A, ACTIVE),
                       PostLabeled(B, ACTIVE))))))

# Other things: more specific phosphorylation (serine-phosphorylated;
# serine-phosphorylated-at). Can prove theorems about this.

# Other theorems to prove: can't have phosphorylated_is_active and not
# phosphorylated_is_active.

# Use cases for reductions (from transitive closure to minimal set of rules)
# Use cases for inconsistency of rules with each other
# Link to INDRA statements
