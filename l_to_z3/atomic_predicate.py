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

def LabeledClassGenerator(name, pre=None, un=None):
    assert pre is not None
    assert un is not None

    class GeneratedClass(AtomicPredicate):
        def __init__(self, var, label, *args):
            AtomicPredicate.__init__(self, *args)
            _ensure_variable(var)
            _ensure_string(label)
            self.label = label
            self.label_as_int = string_interner.get_int_or_add(self.label)
            self.var = var

        def _assert(self, submodel, interpretation):
            if pre:
                labelmap = Graph.labelmap(Model.pregraph(submodel))
            else:
                labelmap = Graph.labelmap(Model.postgraph(submodel))
            node = interpretation(self.var)
            labelset = z3.Select(labelmap, node)
            label = self.label_as_int
            has_label = z3.Select(labelset, label)
            if un:
                return z3.Not(has_label)
            else:
                return has_label

    GeneratedClass.__name__ = name
    return GeneratedClass

PreLabeled = LabeledClassGenerator('PreLabeled', pre=True, un=False)
PostLabeled = LabeledClassGenerator('PostLabeled', pre=False, un=False)
PreUnlabeled = LabeledClassGenerator('PreUnlabeled', pre=True, un=True)
PostUnlabeled = LabeledClassGenerator('PostUnlabeled', pre=False, un=True)

def EdgeClassGenerator(name, pre=None, parent=None):
    assert pre is not None
    assert parent is not None

    class GeneratedClass(AtomicPredicate):
        def __init__(self, x, y, *args):
            AtomicPredicate.__init__(self, *args)
            _ensure_variable(x)
            _ensure_variable(y)
            self.x = x
            self.y = y

        def _assert(self, submodel, interpretation):
            if pre:
                graph = Model.pregraph(submodel)
            else:
                graph = Model.postgraph(submodel)
            edge = Edge.edge(interpretation(self.x), interpretation(self.y))
            if parent:
                function = Graph.parents(graph)
            else:
                function = Graph.links(graph)
            has_edge = z3.Select(function, edge)
            return has_edge

    GeneratedClass.__name__ = name
    return GeneratedClass

PreParent = EdgeClassGenerator('PreParent', pre=True, parent=True)
PostParent = EdgeClassGenerator('PostParent', pre=False, parent=True)
PreLink = EdgeClassGenerator('PreLink', pre=True, parent=False)
PostLink = EdgeClassGenerator('PostLink', pre=False, parent=False)

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
        node = interpretation(self.x)
        has_node = z3.Select(has_function, node)
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
        graph = Model.postgraph(submodel)
        has_function = Graph.has(graph)
        node = interpretation(self.x)
        has_node = z3.Select(has_function, node)
        return has_node


class Add(AtomicPredicate):
    """
    Add a node.
    """
    def __init__(self, x, *args):
        super(Add, self).__init__(*args)
        _ensure_variable(x)
        self.x = x

    def _assert(self, submodel, interpretation):
        node = interpretation(self.x)

        action = Model.action(submodel)
        atomic_action = AtomicAction.add_action(node)
        has_add_action = z3.Select(action, atomic_action)

        graph = Model.pregraph(submodel)
        has_function = Graph.has(graph)
        pregraph_has_node = z3.Select(has_function, node)

        return has_add_action and z3.Not(pregraph_has_node)


class Rem(AtomicPredicate):
    """
    Remove a node.
    """
    def __init__(self, x, *args):
        super(Rem, self).__init__(*args)
        _ensure_variable(x)
        self.x = x

    def _assert(self, submodel, interpretation):
        node = interpretation(self.x)

        action = Model.action(submodel)
        atomic_action = AtomicAction.rem_action(node)
        has_rem_action = z3.Select(action, atomic_action)

        graph = Model.pregraph(submodel)
        has_function = Graph.has(graph)
        pregraph_has_node = z3.Select(has_function, node)

        return has_rem_action and pregraph_has_node


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
