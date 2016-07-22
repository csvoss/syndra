Syndra
===
[![Build Status](https://travis-ci.org/csvoss/syndra.svg?branch=master)](https://travis-ci.org/csvoss/syndra)

Syndra is an **inference engine** for rule-based biological models.

It supports making inferences over sets of modeling rules, which allows **redundancies** to be detected and eliminated from those rules. For example, if we have the rules `MEK phosphorylates MAPK` and `MAPK, when phosphorylated, is active`, Syndra can confirm that these rules imply `MEK activates MAPK`.

Syndra can also detect when a set of rules are **mutually incompatible**. For example, Syndra can detect that no model is compatible with the two rules `A, when phosphorylated, is active` and `A, when phosphorylated, is inactive` both at once.

This system works by translating each rule into predicates in the ***iota*** language, a logic designed by Adrien Husson and Jean Krivine to describe predicates over rule-based biological models. Inferences about these predicates are then powered by the [**z3 theorem prover**](https://github.com/Z3Prover/z3).

[Diagram of Syndra dependencies and architecture.](https://github.com/csvoss/syndra/blob/master/engine/dependencies.pdf)

Constructing predicates
---

Here are three different ways to construct a predicate in Syndra; once a predicate
has been constructed, it can be used to make inferences.

### 1: From INDRA

[**INDRA**](https://github.com/sorgerlab/indra) is a system that can gather statements (rules) for rule-based modeling from natural language and from databases; these statements are represented by INDRA as Python objects. Syndra predicates can be automatically generated from a subset of INDRA statements. This functionality is provided by `interface_indra_to_syndra.py`.

Here I'll show how to use Syndra with INDRA in order to prove that `MEK phosphorylates MAPK at Thr183`, `MEK phosphorylates MAPK at Tyr185`, and `MAPK, when phosphorylated at Thr183 and Tyr185, is active` all together imply `MEK activates MAPK`.

Suppose we have the following INDRA statements corresponding, in order, to these rules:

```python
>>> s1
Phosphorylation(MAP2K1, MAPK1, PhosphorylationThreonine, 183)
>>> s2
Phosphorylation(MAP2K1, MAPK1, PhosphorylationTyrosine, 185)
>>> s3
ActivityModification(MAPK1, ['PhosphorylationThreonine', 'PhosphorylationTyrosine'], ['183', '185'], increases, Activity)
>>> s4
ActivityActivity(MAP2K1, Kinase, increases, MAPK1, Kinase)
```

We want to show that `s1`, `s2`, and `s3` all together imply `s4`. We can generate a Syndra predicate that combines the first three together:

```python
>>> from interface_indra_to_syndra import syndra_from_statements
>>> pred = syndra_from_statements(s1, s2, s3)
```

Then, we can check that these statements are mutually consistent, and also check that they imply `s4`. See *Manipulating predicates* for other things that can be done using predicates.

```python
>>> pred.check_sat()   ## Consistency check
True
```

```python
>>> p4 = syndra_from_statements(s4)   ## Implication check
>>> pred.check_implies(p4)
True
```

### 2: From Syndra macros

Syndra provides a number of *macros*, ways to easily construct Syndra predicates describing common biological rules. The current supported macros are `directly_phosphorylates`, `directly_activates`, and `phosphorylated_is_active` – these being sufficient to implement the INDRA motivating example.

```python
>>> from engine import macros
>>> p1 = macros.directly_phosphorylates("A", "B")
>>> p2 = macros.phosphorylated_is_active("B")
>>> p3 = macros.directly_activates("A", "B")
>>> from engine import predicate
>>> predicate.And(p1, p2).check_implies(p3)
True
```

### 3: Writing an *iota* predicate directly

It is also possible to construct your own macros by writing *iota* predicates using Syndra. Consult `new_engine/predicate.py` for a list of building blocks (subclasses of `Predicate`) that can be used to construct predicates.


Manipulating predicates
---

### Creating a solver

### Check satisfiability

If a predicate is satisfiable, that means that there is at least one way to build a model that satisfies that predicate. You can check whether this is true for any given Syndra predicate using `.check_sat()`.

```python
>>> satisfiable = predicate.Top()
>>> satisfiable.check_sat()
True
>>> unsatisfiable = predicate.Bottom()
>>> unsatisfiable.check_sat()
False
```

### Get model

For a satisfiable predicate, you can also extract a specific example of a model that adheres to that predicate using `.get_model()`.

Currently the models that are returned by this use z3's datatypes; future work may involve translating these to a more friendly format.

### Check implication

Syndra can verify whether one predicate logically implies the truth of another predicate using `.check_implies(other)`.

```python
>>> pred1 = predicate.Top()
>>> pred2 = predicate.Top()
>>> pred1.check_implies(pred2)
True
```

Installation instructions
---

You will need to install Z3. Follow the Z3 installation instructions at [Z3Prover/z3](https://github.com/Z3Prover/z3), being sure to install the Python bindings:

```
git clone https://github.com/Z3Prover/z3
cd z3
virtualenv venv
source venv/bin/activate
python scripts/mk_make.py --python
cd build
make
make install
```

Then, install Syndra itself.

To install Syndra as a pip package: TODO make this a pip-installable package, then put instructions here

Otherwise, to install this code locally:

```
git clone https://github.com/csvoss/syndra/
cd syndra
virtualenv venv
source venv/bin/activate
pip install -r requirements.txt
```

You also need to install INDRA dependencies if you are planning to test Syndra on INDRA statements; consult the instructions [here](https://github.com/sorgerlab/indra).

