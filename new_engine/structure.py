import z3

import datatypes
from string_interner import string_interner, node_interner

class Structure(object):
    def __init__(self):
        raise NotImplementedError("Structure is an abstract class.")

    def _assert(self, graph):
        raise NotImplementedError("Implement _assert in subclasses.")

    def bound(self, other_structure):
        # return a new Structure object
        return Bound(self, other_structure)

    def labeled(self, label):
        # return a new Structure object
        return Labeled(self, label)

    def with_site(self, other_structure):
        # return a new Structure object
        return WithSite(self, other_structure)


class Agent(Structure):
    def __init__(self, name):
        self.name = name

    def central_node_label(self):
        return self.name

    def _assert(self, graph):
        has = datatypes.Graph.has(graph)
        node = node_interner.get_node_or_add(self.central_node_label())
        has_node = z3.Select(has, node)
        return has_node


class Bound(Structure):
    def __init__(self, structure_1, structure_2):
        self.structure_1 = structure_1
        self.structure_2 = structure_2

    def central_node_label(self):
        return self.structure_1.central_node_label()

    def _assert(self, graph):
        links = datatypes.Graph.links(graph)
        node_1 = node_interner.get_node_or_add(self.structure_1.central_node_label())
        node_2 = node_interner.get_node_or_add(self.structure_2.central_node_label())
        edge = datatypes.Edge.edge(node_1, node_2)
        has_link = z3.Select(links, edge)
        return z3.And(has_link,
                self.structure_1._assert(graph),
                self.structure_2._assert(graph))


class WithSite(Structure):
    def __init__(self, structure_1, structure_2):
        self.structure_1 = structure_1
        self.structure_2 = structure_2

    def central_node_label(self):
        return self.structure_1.central_node_label()

    def _assert(self, graph):
        parents = datatypes.Graph.parents(graph)
        node_1 = node_interner.get_node_or_add(self.structure_1.central_node_label())
        node_2 = node_interner.get_node_or_add(self.structure_2.central_node_label())
        edge = datatypes.Edge.edge(node_1, node_2)
        has_parent = z3.Select(parents, edge)
        return z3.And(has_parent,
                self.structure_1._assert(graph),
                self.structure_2._assert(graph))


class Labeled(Structure):
    def __init__(self, structure, label):
        self.structure = structure
        self.label = label
        self.label_as_number = string_interner.get_int_or_add(self.label)

    def central_node_label(self):
        return self.structure.central_node_label()

    def _assert(self, graph):
        labelmap = datatypes.Graph.labelmap(graph)
        node = node_interner.get_node_or_add(self.structure.central_node_label())
        labelset = z3.Select(labelmap, node)  # returns a labelset
        label = self.label_as_number
        label_present = z3.Select(labelset, label) # returns a bool
        return z3.And(label_present,
                self.structure._assert(graph))


def Label(label_string):
    # just to make sure nobody gets messy with using strings as labels -- use
    # variables as labels instead, so that Python raises an error if you misspell
    return "label_" + label_string
