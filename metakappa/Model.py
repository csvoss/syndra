"""Definitions for L language.

.. moduleauthor:: Jean Yang <jean_yang@hms.harvard.edu>
"""
from sets import Set
import itertools

class GraphAction:
    """
    Graph actions.
    """
    def doAction(action):
        raise NotImplementedError("Must implement in subclasses")
class GraphId(GraphAction):
    def doAction(action):
        pass
class GraphUnaryAction(GraphAction):
    def __init__(a):
        self.a = a
class GraphBinaryAction(GraphAction):
    def __init__(a, b):
        self.a = a
        self.b = b
class GraphAdd(GraphUnaryAction):
    def doAction(self, action):
        action.ag_add = Set([self.a])
class GraphRem(GraphUnaryAction):
    def doAction(self, action):
        action.ab_sub = Set([self.a])
class GraphLink(GraphBinaryAction):
    def doAction(self, action):
        action.ag_add = Set([self.a, self.b])
        action.ln_add = Set([Set([self.a, self.b])])
class GraphUnlink(GraphBinaryAction):
    def doAction(self, action):
        action.ln_sub = Set([Set([self.a, self.b])])
class GraphAddSite(GraphBinaryAction):
    def doAction(self, action):
        action.ag_add = Set([self.a, self.b])
        action.pl_add = Set([Set([self.a, self.b])])
class GraphRemoveSite(GraphBinaryAction):
    def doAction(self, action):
        action.pl_sub = Set([Set([self.a, self.b])])

class Action:
    """An action \alpha is a 6-tuple of the form <ag+, ag-, ln+, ln-, pl+, pl->
    which is either an atomic action or the sum of actions.
    """
    def __init__(self, action):
        self.ag_add = Set()
        self.ab_sub = Set()
        self.ln_add = Set()
        self.ln_sub = Set()
        self.pl_add = Set()
        self.pl_sub = Set()

        action.doAction(self)

class Node:
    def __init__(self, v):
        self.v = v


def default_label(agent_identifier):
    """Takes in agent identifiers, and returns an element of some alphabet.
    For now, just return the agent identifier. It's probably a string."""
    return agent_identifier


# Sigma_1, Sigma_2... Sigma_n.
default_alphabets = []

# The logic is parametrized over some set of alphabets.
alphabets = default_alphabets


class Graph:
    """ A structured graph is a 4-tuple <V, L, P, \lambda> with nodes
    V \subseteq fancyV where:
    1. <V, L> is an undirected graph.
    2. <V, P> is a rooted forest of max depth 3, representing bindings at sites.
    3. \lambda : fancyV |--> \Sigma labels nodes. \lambda has domain fancyV.

    For all graphs g, we say node a is at level i if it has i-1 parents.
    """
    def __init__(self):
        self.__allnodes = Set()     # fancyV (how does this get populated?)

        self.nodes = Set()        # list of nodes
        self.links = Set()        # list of edges
        self.bindings = Set()     # list of bindings (use dict?)
        self.label = default_label  # function which labels nodes

    def __eq__(self, other):
        return self.__allnodes == other.__allnodes and \
            self.nodes == other.nodes and \
            self.links == other.links and \
            self.bindings == other.bindings and \
            self.label == other.label

    @staticmethod
    def unord(s):
        """From Definition 3 of Adrien Husson's report.
        """
        return Set(map(lambda ((a, b)): Set([a, b]), s))

    def applyAction(self, alpha):
        """From Definition 3 of Adrien Husson's report.
        """
        self.nodes.difference_update(alpha.ag_sub)
        self.nodes.union_update(alpha.ag_add)

        self.links.difference_update(alpha.ln_sub)
        self.links.difference_update(
            Graph.unord(itertools.product(alpha.ag_sub, self.__allnodes)))
        self.links.union_update(alpha.ln_add)

        self.bindings.difference_update(alpha.pl_sub)
        self.bindings.difference_update(
            itertools.product(alpha.ag_sub, self.__allnodes))
        self.bindings.difference_update(
            itertools.product(self.__allnodes, alpha.ag_sub))
        self.bindings.union_update(alpha.pl_add)

class Model:
    """ Models are sets of pairs <g, \alpha> where g is a structured graph and
    \alpha is a set of actions.
    """
    def __init__(self):
        self.model = Set()

    def join(self, model2):
        """Definition 4.
        """
        newModel = Set()

        m2_graphs = [seq[0] for seq in model2.model]
        for (graph, action) in self.model:
            if graph in m2_graphs:
                newModel.add((graph, action))

        m1_graphs = [seq[0] for seq in self.model]
        for (graph, action) in model2.model:
            if graph in m1_graphs:
                newModel.add((graph, action))

        return newModel


class Predicate:
    def filter_over(g_set, a_set):
        """
        Return a set of graphs and actions for which the predicate is true.

        Arguments:
            g_set: a set of Graphs
            a_set: a set of Actions

        Returns:
            a set of (Graph, Action) pairs
        """
        assert isinstance(g_set, set)
        for g in g_set:
            assert isinstance(g, Graph)
        assert isinstance(a_set, set)
        for a in a_set:
            assert isinstance(a, Action)
        output = set(filter_over_helper(g_set, a_set))
        for tup in output:
            assert isinstance(tup, tuple) and len(tup) == 2
            g, a = tup
            assert isinstance(g, Graph)
            assert isinstance(a, Action)
        return output

    def filter_over_helper(g_set, a_set):
        raise NotImplementedError("Must implement in subclasses")

    def __init__(self):
        pass

class TopPredicate(Predicate):
    def filter_over_helper(g_set, a_set):
        return itertools.product(g_set, a_set)
class BottomPredicate(Predicate):
    def filter_over_helper(g_set, a_set):
        return set()
class EqualsPredicate(Predicate):
    def __init__(self, I, x, y):
        """[x=y]_I.
        Arguments:
            I: the interpretation? Function from variable -> string, probably.
            x: a variable?
            y: a variable?
        """
        self.x = I(x)
        self.y = I(y)
    def filter_over_helper(g_set, a_set):
        return TopPredicate().filter_over(g_set, a_set) if (self.x == self.y)
                else BottomPredicate().filter_over(g_set, a_set)
class SigmaPredicate(Predicate):
    def __init__(self, I, sigma, x):
        """[\Sigma(x)]_I.
        Arguments:
            I: the interpretation? Function from variable -> string, probably.
            sigma: an alphabet?
            x: a variable?
        """
        self.x = I(x)
        self.sigma = sigma
    def filter_over_helper(g_set, a_set):
        for g in g_set:
            if g.label(x) in self.sigma:
                for a in a_set:
                    yield (g, a)
class LabeledPredicate(Predicate):
    def __init__(self, I, A, x):
        """[A(x)]_I.
        Arguments:
            I: the interpretation? Function from variable -> string, probably.
            A: a label? Same type as the elements of an alphabet (a \Sigma).
            x: a variable?
        """
        pass
