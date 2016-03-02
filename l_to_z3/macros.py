from predicate import PreLabeled, PreUnlabeled, Named, PostLabeled, And, Implies, ForAll
from datatypes import new_variable

from labels import ACTIVE, PHOSPHORYLATED

# Macro for "A" phosphorylates "B"
# forall A. Named("A", A) => forall B. Named("B", B) =>
#     (Labeled(A, "Active") /\ Unlabeled(B, "Phosphorylated") /\
#     PostLabeled(A, "Active") /\ PostLabeled(B, "Phosphorylated"))
def directly_phosphorylates(name_a, name_b):
    A = new_variable(name_a)
    B = new_variable(name_b)
    return ForAll(A, ForAll(B,
           Implies(Named(A, name_a), Implies(Named(B, name_b),
           And(PreLabeled(A, ACTIVE),
               PreUnlabeled(B, PHOSPHORYLATED),
               PostLabeled(A, ACTIVE),
               PostLabeled(B, PHOSPHORYLATED))))))

# Macro for Phosphorylated "B" is active
# forall B. Named("B", B) =>
#     (PreLabeled(B, "Phosphorylated") => PreLabeled(B, "Active")) and
#     (PostLabeled(B, "Phosphorylated") => PostLabeled(B, "Active"))
def phosphorylated_is_active(name_b):
    B = new_variable(name_b)
    return NotImplemented

# Macro for "A" activates "B"
# forall A. Named("A", A) => forall B. Named("B", B) =>
#     (Labeled(A, "Active") /\ Unlabeled(B, "Active") /\
#     PostLabeled(A, "Active") /\ PostLabeled(B, "Active"))
def directly_activates(name_a, name_b):
    A = new_variable(name_a)
    B = new_variable(name_b)
    return ForAll(A, ForAll(B,
           Implies(Named(A, name_a), Implies(Named(B, name_b),
           And(PreLabeled(A, ACTIVE),
               PreUnlabeled(B, ACTIVE),
               PostLabeled(A, ACTIVE),
               PostLabeled(B, ACTIVE))))))
