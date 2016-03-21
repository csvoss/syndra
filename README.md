Syndra
===

Syndra is an **inference engine** for rule-based biological models.

It supports making inferences over sets of modeling rules, which allows **redundancies** to be detected and eliminated from those rules. For example, if we have the rules `MEK phosphorylates MAPK` and `MAPK, when phosphorylated, is active`, Syndra can confirm that these rules imply `MEK activates MAPK`.

Syndra can also detect when a set of rules are **mutually incompatible**. For example, Syndra can detect that no model is compatible with the two rules `A, when phosphorylated, is active` and `A, when phosphorylated, is inactive` both at once.

This system works by translating each rule into predicates in the ***iota*** language, a logic designed by Adrien Husson and Jean Krivine to describe predicates over rule-based biological models. Inferences about these predicates are then powered by the [**z3 theorem prover**](https://github.com/Z3Prover/z3).

![Diagram of Syndra dependencies and architecture.](https://github.com/csvoss/syndra/blob/master/l_to_z3/dependencies.pdf)

Constructing predicates
---

Here are three different ways to construct a predicate in Syndra; once a predicate
has been constructed, it can be used to make inferences (see *Manipulating predicates*, below).

### From INDRA

Here I'll show how to use Syndra with INDRA in order to prove the

[How to use Syndra for INDRA statements, with example usage and outputs.]

### From macros

[List of macro interfaces, with example usage and outputs.]

### Writing an *iota* predicate directly

It is also possible to construct your own *iota* predicates using Syndra. Consult `l_to_z3/predicate.py` for a list of building blocks (subclasses of `Predicate`) that can be used to construct predicates. See ***iota* basics**, below, for a description of what these predicates mean and how they work.

Manipulating predicates
---

[How to check_sat, get_model, etc. from a predicate.]



*iota* basics
---
[How L works, a brief summary: discuss how L predicates correspond to models in L, and what those models mean as Kappa models.]

Installation instructions
---

```
git clone https://github.com/csvoss/syndra/
source venv/bin/activate
pip install requirements.txt
```

You need to install INDRA dependencies in order to test Syndra on INDRA statements; consult the instructions [here](https://github.com/sorgerlab/indra).

```
python interface_indra_to_syndra.py
```

To test Syndra macros more directly, without passing through INDRA:

```
cd l_to_z3
python test_macros.py
```
