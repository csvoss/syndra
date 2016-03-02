from predicate import PreLabeled, PreUnlabeled, Named, PostLabeled, And, Implies, Forall
from datatypes import new_variable

# TODO: something like from labels import Active so that you don't have to use raw strings

# Macro for "A" phosphorylates "B"
# forall A. Named("A", A) => forall B. Named("B", B) =>
#     (Labeled(A, "Active") /\ Unlabeled(B, "Phosphorylated") /\
#     PostLabeled(A, "Active") /\ PostLabeled(B, "Phosphorylated"))
def directly_phosphorylates(name_a, name_b):
    A = new_variable(name_a)
    B = new_variable(name_b)
    return Forall(A, Forall(B,
           Implies(Named(A, name_a), Implies(Named(B, name_b),
           And(PreLabeled(A, "Active"),
               PreUnlabeled(B, "Phosphorylated"),
               PostLabeled(A, "Active"),
               PostLabeled(B, "Phosphorylated"))))))

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
    return NotImplemented
