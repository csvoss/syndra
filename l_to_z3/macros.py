# Macro for "A" phosphorylates "B"
# forall A. Named("A", A) => forall B. Named("B", B) =>
#     (Labeled(A, "Active") /\ Unlabeled(B, "Phosphorylated") /\
#     PostLabeled(A, "Active") /\ PostLabeled(B, "Phosphorylated"))

# Macro for Phosphorylated "B" is active
# forall B. Named("B", B) =>
#     (PreLabeled(B, "Phosphorylated") => PreLabeled(B, "Active")) and
#     (PostLabeled(B, "Phosphorylated") => PostLabeled(B, "Active"))

# Macro for "A" activates "B"
# forall A. Named("A", A) => forall B. Named("B", B) =>
#     (Labeled(A, "Active") /\ Unlabeled(B, "Active") /\
#     PostLabeled(A, "Active") /\ PostLabeled(B, "Active"))
