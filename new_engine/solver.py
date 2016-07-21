#pylint: disable=attribute-defined-outside-init,too-many-locals,too-many-instance-attributes
"""
Solver for reasoning about Syndra predicates.
"""
import contextlib
import itertools
import z3
import z3types

import predicate
import interners

class MySolver(object):
    """
    This class allows you to create instances of solvers, which manage their
    own state. Solvers are for reasoning about the satisfiability of
    Syndra predicates.

    The design of this solver is inspired by the methods provided by z3's
    solver.
    """
    # TODO: Redesign this class so that it does not assume that the first
    # predicate it gets will contain all of the nodes it needs to know about.

    def __init__(self, *node_names):
        """
        The solver must be instantiated with a list of agent names
        you intend to use.
        """
        try:
            self._solver = z3.Solver()
        except:
            raise ImportError("You must have Z3 installed. Have you activated your virtualenv?")
        self.node_names = node_names
        self._attach_datatypes()
        self.model_variable = self.new_model()
        self.string_interner = interners.StringInterner()

    def push(self):
        """Push solver state."""
        self._solver.push()

    def pop(self):
        """Pop solver state."""
        self._solver.pop()

    def add(self, syndra_predicate):
        """Add a Syndra predicate to the solver state.

        Arguments:
            syndra_predicate : Syndra predicate, instance of predicate.Predicate
        """
        # Add the predicate's nodes to self.node_names
        self.add_nodes_from(syndra_predicate)

        # Add the predicate iself to Z3
        z3_predicate = syndra_predicate.get_predicate(self.model_variable, self)
        self._solver.add(z3_predicate)

    def add_nodes_from(self, syndra_predicate):
        """
        Add the nodes in syndra_predicate to our list of nodes.
        """
        # Traverse the predicate to get names of agents it contains
        # Append those agent names to self.node_names
        # If we have more nodes now, re-call self._attach_datatypes
        # This will involve messing with the z3 solver state and
        # re-adding a bunch of predicates to it
        # TODO implement this
        pass

    def _add_z3(self, z3_predicate):
        """Add a z3 predicate to the solver state.

        Arguments:
            z3_predicate : Z3-friendly predicate or boolean
        """
        return self._solver.add(z3_predicate)

    def model(self):
        """Return a model for the current solver state.

        Returns :: set of RuleResult objects
        """
        self._model_z3()

        ## EXTRA ASSERTIONS

        def try_assertion(edge_assertion):
            with self.context():
                self._add_z3(edge_assertion)
                satisfiable = self.check()
            if satisfiable:
                print "Constraint added!", edge_assertion
                self._add_z3(edge_assertion)
            else:
                print "Too constraining!", edge_assertion

        # This is to check that I can assert stuff at all.
        try_assertion(z3.And(True))

        g = z3.Const('testgraph', self.Graph)
        n1 = self.new_node()
        n2 = self.new_node()

        # These are some sanity constraints.
        try_assertion(z3.Implies(z3.Select(self.Graph.links(g), self.Edge.edge(n1, n2)), z3.Select(self.Graph.has(g), n1)))
        try_assertion(z3.Implies(z3.Select(self.Graph.links(g), self.Edge.edge(n1, n2)), z3.Select(self.Graph.has(g), n2)))
        try_assertion(z3.Implies(z3.Or(*map(lambda a: a==n1, self.nodes.values())), z3.Select(self.Graph.has(g), n1)))
        try_assertion(z3.Implies(z3.Select(self.Graph.has(g), n1), z3.Or(*map(lambda a: a==n1, self.nodes.values()))))

        # Edges must be symmetric.
        try_assertion(z3.Implies(z3.Select(self.Graph.links(g), self.Edge.edge(n1, n2)), z3.Select(self.Graph.links(g), self.Edge.edge(n2, n1))))

        mo = self._solver.model()
        rules = [i[0] for i in mo[self.model_variable].as_list()[:-1]]
        # These attempt to minimize the number of edges.
        for rule in rules:
            prg = self.Rule.pregraph(rule)
            pog = self.Rule.postgraph(rule)
            prlinks = self.Graph.links(prg)
            prparents = self.Graph.parents(prg)
            polinks = self.Graph.links(pog)
            poparents = self.Graph.parents(pog)
            for agent_1 in self.nodes.values():
                for agent_2 in self.nodes.values():
                    edge = self.Edge.edge(agent_1, agent_2)
                    try_assertion(z3.Not(z3.Select(prparents, edge)))
                    try_assertion(z3.Not(z3.Select(poparents, edge)))
                    try_assertion(z3.Not(z3.Select(prlinks, edge)))
                    try_assertion(z3.Not(z3.Select(polinks, edge)))



        ## MODEL-GETTING

        model = self._model_z3()
        output = []
        rules = model[self.model_variable].as_list()
        if not isinstance(rules[-1], list):
            # For some reason the last element of 'rules' is usually True
            rules = rules[:-1]
        for pair in rules:
            rule, rule_in_model = pair[0], pair[1]
            assert rule_in_model # This says the rule is in the model
            output.append(RuleResult(rule, model, self))
        return output


    def _model_z3(self):
        """Return a model for the current solver state, straight from z3.

        Returns :: Z3 model.
        """
        try:
            return self._solver.model()
        except z3types.Z3Exception:
            raise ValueError("Tried to get model of unsat!")

    def check(self):
        """Check satisfiability of current satisfiability state.

        Returns :: boolean -- True if sat, False if unsat
        """
        # check() returns either unsat or sat
        result = self._solver.check().r
        # sat.r is 1, unsat.r is -1
        if result > 0:
            return True
        elif result < 0:
            return False
        else:
            raise Exception("z3 returned unknown")

    @contextlib.contextmanager
    def context(self):
        """To do something in between a push and a pop, use a `with context()`.
        This is especially useful for avoiding bugs caused by forgetting pop().
        """
        self.push()
        yield
        self.pop()

    def quick_check(self, syndra_predicate):
        """Check if a predicate is satisfiable without changing solver state."""
        with self.context():
            self.add(syndra_predicate)
            return self.check()

    def quick_check_sat(self, syndra_predicate):
        """See the documentation for quick_check(...)."""
        return self.quick_check(syndra_predicate)

    def quick_check_valid(self, syndra_predicate):
        """Quickcheck that a predicate is valid - that its negation is unsat."""
        with self.context():
            if not self.check():
                return True # The predicate is implied by the unsat env
            self.add(predicate.Not(syndra_predicate))
            return not self.check() # if negation is unsat, then it's valid

    def _labelset_to_set_of_labels(self, labelset, model):
        """
        Given a z3 labelset from a model, extract a set of labels.
        """
        output = []
        for i in range(1, self.string_interner.counter):
            if str(model.evaluate(z3.Select(labelset, i))) == 'True': # bleh
                thing = self.string_interner.get_str(i)
                if "label_" in thing:
                    output.append(thing[6:])
        return output

    def _attach_datatypes(self):
        self.Node, self.node_values = z3.EnumSort("Node", self.node_names)

        self.nodes = dict(zip(self.node_names, self.node_values))

        # A datatype for storing a pair of edges
        self.Edge = z3.Datatype('Edge')
        self.Edge.declare('edge',
                          ('node1', self.Node),
                          ('node2', self.Node))
        self.Edge = self.Edge.create()

        self.Nodeset = z3.ArraySort(self.Node, z3.BoolSort())
        self.Edgeset = z3.ArraySort(self.Edge, z3.BoolSort())

        self.Labelset = z3.ArraySort(z3.IntSort(), z3.BoolSort())
        self.Labelmap = z3.ArraySort(self.Node, self.Labelset)

        # Graph, before a rule or action has applied. Merged Pregraph and Postgraph
        # into a single datatype.
        self.Graph = z3.Datatype('Graph')
        self.Graph.declare('graph',
                           ('has', self.Nodeset),
                           ('links', self.Edgeset),
                           ('parents', self.Edgeset),
                           ('labelmap', self.Labelmap))
        self.Graph = self.Graph.create()

        # This represents a set of possible <pregraph, postgraph> pairs.
        self.Rule = z3.Datatype('Rule')
        self.Rule.declare('rule',
                          ('pregraph', self.Graph),
                          ('postgraph', self.Graph))
        self.Rule = self.Rule.create()

    def new_rule(self, nickname='rule'):
        """Create a new z3 Rule constant."""
        return z3.Const(_collision_free_string(nickname), self.Rule)

    def new_model(self, nickname='model'):
        """Create a new model to assert predicates over."""
        return z3.Function(_collision_free_string(nickname), self.Rule, z3.BoolSort())

    def new_node(self, nickname='node'):
        """Create a new z3 Node constant."""
        return z3.Const(_collision_free_string(nickname), self.Node)



# MODEL RESULTS

class RuleResult(object):
    """
    Stores a rule and its pregraph/postgraph, for examining a z3-produced model.
    """
    def __init__(self, rule, model, solver):
        pregraph = solver.Rule.pregraph(rule)
        postgraph = solver.Rule.postgraph(rule)
        self.pregraph = GraphResult(pregraph, model, solver)
        self.postgraph = GraphResult(postgraph, model, solver)

    def __repr__(self):
        return "Rule(%s -> %s)" % (str(self.pregraph), str(self.postgraph))


class GraphResult(object):
    """
    Stores a graph and its links, for examining a z3-produced model.
    """
    def __init__(self, graph, model, solver):
        nodes = []

        agent_names = solver.nodes.keys()

        has = solver.Graph.has(graph)
        links = solver.Graph.links(graph)
        parents = solver.Graph.parents(graph)
        labelmap = solver.Graph.labelmap(graph)

        for agent_name in agent_names:
            z3_node = solver.nodes[agent_name]
            has_some_node = model.evaluate(z3.Select(has, z3_node))
            if has_some_node:
                labels = model.evaluate(z3.Select(labelmap, z3_node))
                labels = solver._labelset_to_set_of_labels(labels, model)
                nodes.append(NodeResult(z3_node, agent_name, labels))

        for node_1 in nodes:
            for node_2 in nodes:
                if node_1 != node_2:
                    edge = solver.Edge.edge(node_1.z3_node, node_2.z3_node)
                    edge_in_parents = model.evaluate(z3.Select(parents, edge))
                    edge_in_links = model.evaluate(z3.Select(links, edge))
                    if str(edge_in_parents) == 'True':
                        node_1.add_site(node_2)
                    if str(edge_in_links) == 'True':
                        node_1.add_link(node_2)

        self.nodes = nodes

    def __repr__(self):
        return "{%s}" % ('; '.join(str(node) for node in self.nodes))


class NodeResult(object):
    """
    Stores a node and its properties, for examining a z3-produced model.
    """
    def __init__(self, z3_node, name, labels):
        self.z3_node = z3_node
        self.name = name
        self.labels = labels
        self.links = []
        self.sites = []

    def add_link(self, other_node):
        """Add an edge between this node and another node."""
        self.links.append(other_node)

    def add_site(self, other_node):
        """Add a parent edge from this node to another node."""
        self.sites.append(other_node)

    def __repr__(self):
        output = self.name
        if len(self.labels) > 0:
            output += ("-(%s)" % (', '.join(self.labels)))
        if len(self.links) > 0:
            output += " with links to " + (', '.join(link.name for link in self.links))
        if len(self.sites) > 0:
            output += " with sites " + (', '.join(site.name for site in self.sites))
        return output


_numbergen = itertools.count(start=1, step=1)

def _collision_free_string(prefix=""):
    return prefix + "_" + str(_numbergen.next())
