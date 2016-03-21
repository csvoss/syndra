Syndra
===

Syndra is an **inference engine** for rule-based biological models. It supports making inferences over sets of modeling rules, which allows **redundancies** to be detected and eliminated from those rules. For example, if we have the rules `MEK phosphorylates MAPK` and `MAPK, when phosphorylated, is active`, Syndra can confirm that these rules imply `MEK activates MAPK`.

Syndra can also detect when a set of rules are **mutually incompatible**. For example, Syndra can detect that no model is compatible with the two rules `A, when phosphorylated, is active` and `A, when phosphorylated, is inactive` both at once.

This system works by translating each rule into predicates in the *iota* language, a logic designed by Adrien Husson and Jean Krivine to describe predicates over rule-based biological models. Inferences are then powered by the z3 theorem prover.


Example Usage
---

TOP LAYER: How to use Syndra: list of commands for macro interfaces, with example usage and outputs
 - Example usage of macro interfaces
 - List of macro interfaces
 - Example usage of macro interfaces *with INDRA in particular*

MIDDLE LAYER: How Syndra works: description of the implementation of L predicates, list of predicates

DIAGRAM (optional): map of dependencies among Python files of Syndra

DIAGRAM (optional): example of how the AST parsing works, and the interface between predicates and atomic predicates, and how it all gets represented as a z3 formula

BOTTOM LAYER: How L works, a brief summary: discuss how L predicates correspond to models in L, and what those models mean as Kappa models.

Maybe also add installation instructions and a list of features-in-progress at the end.
