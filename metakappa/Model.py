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
        pass
class GraphId(GraphAction):
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
    def __init__(self):
        self.ag_add = Set()
        self.ab_sub = Set()
        self.ln_add = Set()
        self.ln_sub = Set()
        self.pl_add = Set()
        self.pl_sub = Set()

    def __init__(self, action):
        self.__init__()
        action.doAction(self)

class Node:
    def __init__(self, v):
        self.v = v

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
        self.labels = []          # hm, what are labels?

    def __eq__(self, other):
        return self.__allnodes == other.__allnodes and \
            self.nodes == other.nodes and \
            self.links == other.links and \
            self.bindings == other.bindings and \
            self.labels == other.labels

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
