"""Definitions for L language.

.. moduleauthor:: Jean Yang <jean_yang@hms.harvard.edu>
"""
from sets import Set

class GraphAction:
    """
    Graph actions.
    """
    pass
class GraphId(GraphAction):
    pass
class GraphAdd(GraphAction):
    def __init__(a):
        self.a = a
class GraphRem(GraphAction):
    def __init__(a):
        self.a = a

class Action:
    """An action \alpha is a 6-tuple of the form <ag+, ag-, ln+, ln-, pl+, pl->
    which is either an atomic action or the sum of actions.
    """
    def __init__(self):
        self.__ag_add = Set()
        self.__ag_sub = Set()
        self.__ln_add = Set()
        self.__ln_sub = Set()
        self.__pl_add = Set()
        self.__pl_sub = Set()

    def __init__(self, action):
        self.__init__()
        if isinstance(action, GraphAdd):
            self.__ag_add.add(action.a)
        elif isinstance(action, GraphRemove):
            self.__ag_sub.add(action.a)


class Graph:
    """ A structured graph is a 4-tuple <V, L, P, \lambda> with nodes
    V \subseteq fancyV where:
    1. <V, L> is an undirected graph.
    2. <V, P> is a rooted forest of max depth 3, representing bindings at sites.
    3. \lambda : fancyV |--> \Sigma labels nodes. \lambda has domain fancyV.

    For all graphs g, we say node a is at level i if it has i-1 parents.
    """
    def __init__(self):
        self.__nodes = []       # list of nodes
        self.__links = []       # list of edges
        self.__bindings = []    # list of bindings (use dict?)
        self.__labels = []      # hm, what are labels?

# Models are sets of pairs <g, \alpha> where g is a structured graph and \alpha
# is a set of actions.
class Model:
    """ Models are sets of pairs <g, \alpha> where g is a structured graph and
    \alpha is a set of actions.
    """
    def __init__(self):
        self.__graph = None
        self.__actions = []
