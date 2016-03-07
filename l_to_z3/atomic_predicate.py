"""
L's atomic predicate: constrains graph-action pairs.

This thing should be an interface implemented by a bunch of different
subclasses; combine those subclasses together to make a predicate, and then
allow the predicate to be executed / checked / model-got / whatever we want by
Z3. This is one abstraction layer higher than the above Z3 definitions are.
Probably the subclasses should only return Z3 formulae, not make any assertions;
then, Predicate can manipulate those formulae into an assertion.

Refer to pg. 7 of the L description.
"""

import z3

from datatypes import (AtomicAction, Action, Edge, Graph, Model,
                       Variable, _ensure_string, _ensure_variable)
from string_interner import string_interner

class AtomicPredicate(object):
    """Parent class which all AtomicPredicates will subclass.

    Contains implementations of some z3-related functionality. Subclasses will
    override get_predicate.
    """

    def __init__(self):
        pass

    def _assert(self, submodel, interpretation):
        # submodel: representation of a set of graph, action pairs
        raise NotImplementedError("Implement _assert in subclasses.")


class Top(AtomicPredicate):
    def _assert(self, submodel, interpretation):
        return z3.And(True, True)


class Bottom(AtomicPredicate):
    def _assert(self, submodel, interpretation):
        return z3.Or(False, False)


class Equal(AtomicPredicate):
    """
    ; Equality of variables x and y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (= (get-varname x) (get-varname y)))
    """
    def __init__(self, x, y, *args):
        super(Equal, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        return (Variable.get_name(self.x) ==
                Variable.get_name(self.y))

class PreLabeled(AtomicPredicate):
    """
    Pregraph variable has specific label.
    """
    def __init__(self, x, label, *args):
        super(PreLabeled, self).__init__(*args)
        _ensure_variable(x)
        _ensure_string(label)
        self.label = label
        self.label_as_int = string_interner.get_int_or_add(self.label)
        self.x = x

    def _assert(self, submodel, interpretation):
        labelmap = Graph.labelmap(Model.pregraph(submodel))
        node = interpretation(self.x)
        labelset = z3.Select(labelmap, node)
        label = self.label_as_int
        has_label = z3.Select(labelset, label)
        return has_label


class PostLabeled(AtomicPredicate):
    """
    Postgraph variable has specific label.
    """
    def __init__(self, x, label, *args):
        super(PostLabeled, self).__init__(*args)
        _ensure_variable(x)
        _ensure_string(label)
        self.label = label
        self.label_as_int = string_interner.get_int_or_add(self.label)
        self.x = x

    def _assert(self, submodel, interpretation):
        labelmap = Graph.labelmap(Model.postgraph(submodel))
        node = interpretation(self.x)
        labelset = z3.Select(labelmap, node)
        label = self.label_as_int
        has_label = z3.Select(labelset, label)
        return has_label


class PreUnlabeled(AtomicPredicate):
    """
    Pregraph variable lacks specific label.
    """
    def __init__(self, x, label, *args):
        super(PreUnlabeled, self).__init__(*args)
        _ensure_variable(x)
        _ensure_string(label)
        self.label = label
        self.label_as_int = string_interner.get_int_or_add(self.label)
        self.x = x

    def _assert(self, submodel, interpretation):
        labelmap = Graph.labelmap(Model.pregraph(submodel))
        node = interpretation(self.x)
        labelset = z3.Select(labelmap, node)
        label = self.label_as_int
        has_label = z3.Select(labelset, label)
        return z3.Not(has_label)


class PostUnlabeled(AtomicPredicate):
    """
    Postgraph variable lacks specific label.
    """
    def __init__(self, x, label, *args):
        super(PostUnlabeled, self).__init__(*args)
        _ensure_variable(x)
        _ensure_string(label)
        self.label = label
        self.label_as_int = string_interner.get_int_or_add(self.label)
        self.x = x

    def _assert(self, submodel, interpretation):
        labelmap = Graph.labelmap(Model.postgraph(submodel))
        node = interpretation(self.x)
        labelset = z3.Select(labelmap, node)
        label = self.label_as_int
        has_label = z3.Select(labelset, label)
        return z3.Not(has_label)


class PreParent(AtomicPredicate):
    """
    ; Variable x has child y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-parents (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PreParent, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        graph = Model.pregraph(submodel)
        edge = Edge.edge(interpretation(self.x), interpretation(self.y))
        parents_function = Graph.parents(graph)
        has_edge = z3.Select(parents_function, edge)
        return has_edge

class Named(AtomicPredicate):
    """
    Variable v refers to an agent that is (permanently) named n.
    """
    def __init__(self, var, name, *args):
        super(Named, self).__init__(*args)
        _ensure_variable(var)
        _ensure_string(name)
        self.var = var
        self.name = name
        self.name_as_number = string_interner.get_int_or_add(self.name)

    def _assert(self, submodel, interpretation):
        return Variable.get_name(self.var) == self.name_as_number

# TODO: To reduce code size, parametrize PreParent and PostParent
# over postgraphness or pregraphness

class PostParent(AtomicPredicate):
    """
    ; "Bar" of "Variable x has child y", which seems to indicate that x has
    ; child y only in the second graph produced by G combined with A.
    ; This is the postcondition!
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-2-parents (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PostParent, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        graph = Model.postgraph(submodel)
        edge = Edge.edge(interpretation(self.x), interpretation(self.y))
        parents_function = Graph.parents(graph)
        has_edge = z3.Select(parents_function, edge)
        return has_edge


class DoParent(AtomicPredicate):
    """
    ; "Do" of "Variable x has child y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (parent-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y, *args):
        super(DoParent, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        action = Model.action(submodel)
        atomic_action = AtomicAction.parent_action(
            interpretation(self.x), interpretation(self.y))
        has_action = z3.Select(action, atomic_action)
        return has_action


class PreLink(AtomicPredicate):
    """
    ; Variable x links to variable y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-links (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PreLink, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        graph = Model.pregraph(submodel)
        edge = Edge.edge(interpretation(self.x), interpretation(self.y))
        links_function = Graph.links(graph)
        has_edge = z3.Select(links_function, edge)
        return has_edge


class PostLink(AtomicPredicate):
    """
    ; "Bar" of Variable x links to variable y; Again a postcondition.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-2-links (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PostLink, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        graph = Model.postgraph(submodel)
        edge = Edge.edge(interpretation(self.x), interpretation(self.y))
        links_function = Graph.links(graph)
        has_edge = z3.Select(links_function, edge)
        return has_edge


class DoLink(AtomicPredicate):
    """
    ; "Do" of "Variable x links to variable y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (link-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y, *args):
        super(DoLink, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        action = Model.action(submodel)
        atomic_action = AtomicAction.link_action(
            interpretation(self.x), interpretation(self.y))
        has_action = z3.Select(action, atomic_action)
        return has_action


class DoUnlink(AtomicPredicate):
    """
    ; "Do" of "Variable x unlinks to variable y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (unlink-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y, *args):
        super(DoUnlink, self).__init__(*args)
        _ensure_variable(x)
        _ensure_variable(y)
        self.x = x
        self.y = y

    def _assert(self, submodel, interpretation):
        action = Model.action(submodel)
        atomic_action = AtomicAction.unlink_action(
            interpretation(self.x), interpretation(self.y))
        has_action = z3.Select(action, atomic_action)
        return has_action


class PreHas(AtomicPredicate):
    """
    ; "Has" of variable x.
    (declare-const x Variable)
    (assert (graph-has (interpretation x)))
    """
    def __init__(self, x, *args):
        super(PreHas, self).__init__(*args)
        _ensure_variable(x)
        self.x = x

    def _assert(self, submodel, interpretation):
        graph = Model.pregraph(submodel)
        has_function = Graph.has(graph)
        has_node = z3.Select(has_function, self.x)
        return has_node


class PostHas(AtomicPredicate):
    """
    ; "Bar" of "Has" of x. Again, a postcondition.
    (declare-const x Variable)
    (assert (graph-2-has (interpretation x)))
    """
    def __init__(self, x, *args):
        super(PostHas, self).__init__(*args)
        _ensure_variable(x)
        self.x = x

    def _assert(self, submodel, interpretation):
        return Model.postgraph(submodel).has(
            interpretation(self.x))


class Add(AtomicPredicate):
    """
    Add a node.
    """
    def __init__(self, x, *args):
        super(Add, self).__init__(*args)
        _ensure_string(x)
        self.x = x

    def _assert(self, submodel, interpretation):
        return (Model.action(submodel).has(AtomicAction.add_action(interpretation(x)))
            and not Model.pregraph(submodel).has(interpretation(x)))

class Rem(AtomicPredicate):
    """
    Remove a node.
    """
    def __init__(self, x, *args):
        super(Rem, self).__init__(*args)
        _ensure_variable(x)
        self.x = x

    def _assert(self, submodel, interpretation):
        return (Model.action(submodel).has(AtomicAction.rem_action(interpretation(x)))
            and Model.pregraph(submodel).has(interpretation(x)))



# Helper functions.

def z3_accessor(func, item):
    """Apply func and read out the accessed value of a z3 datatype, if the
    value for that accessor was an IntSort().

    Arguments:
        func :: a z3 accessor function
        item :: a z3 datatype instance
    Returns:
        :: long - the accessed value
    """
    return func(item).children()[0].children()[0].as_long()




def _ensure_atomic_predicate(thing):
    """Raise ValueError if thing is not an instance of AtomicPredicate."""
    if not isinstance(thing, AtomicPredicate):
        raise ValueError("Arguments must be instances of AtomicPredicate. Instead, got %s" % repr(thing))
