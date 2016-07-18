import z3

from datatypes import Rule, Graph, Edge
from string_interner import string_interner, node_interner

def pythonized(pred, model):
    # Return a list of Rule objects
    # Apply the interpretation everywhere
    output = []
    rules = model[pred.model_variable].as_list()
    if type(rules[-1]) is not list:
        # For some reason the last element of 'rules' is usually True
        rules = rules[:-1]

    for pair in rules:
        rule, rule_in_model = pair[0], pair[1]
        assert rule_in_model # This says the rule is in the model
        output.append(RuleResult(rule, model))

    return output


class RuleResult(object):
    def __init__(self, rule, model):
        pregraph = Rule.pregraph(rule)
        postgraph = Rule.postgraph(rule)
        self.pregraph = GraphResult(pregraph, model)
        self.postgraph = GraphResult(postgraph, model)

    def __repr__(self):
        return "Rule(%s -> %s)" % (str(self.pregraph), str(self.postgraph))


class GraphResult(object):
    def __init__(self, graph, model):

        nodes = []

        agent_names = node_interner._str_to_node.keys()

        has = Graph.has(graph)
        links = Graph.links(graph)
        parents = Graph.parents(graph)
        labelmap = Graph.labelmap(graph)

        for agent_name in agent_names:
            z3_node = node_interner.get_node(agent_name)
            has_some_node = model.evaluate(z3.Select(has, z3_node))
            if has_some_node:
                labels = model.evaluate(z3.Select(labelmap, z3_node))
                labels = labelset_to_set_of_labels(labels, model)
                nodes.append(NodeResult(z3_node, agent_name, labels))

        for node_1 in nodes:
            for node_2 in nodes:
                if node_1 != node_2:
                    edge = Edge.edge(node_1.z3_node, node_2.z3_node)
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
    def __init__(self, z3_node, name, labels):
        self.z3_node = z3_node
        self.name = name
        self.labels = labels
        self.links = []
        self.sites = []

    def add_link(self, other_node):
        self.links.append(other_node)

    def add_site(self, other_node):
        self.links.append(other_node)

    def __repr__(self):
        output = self.name
        if len(self.labels) > 0:
            output += ("-(%s)" % (', '.join(self.labels)))
        if len(self.links) > 0:
            output += " with links to " + (', '.join(link.name for link in self.links))
        if len(self.sites) > 0:
            output += " with sites " + (', '.join(site.name for site in self.sites))
        return output

def labelset_to_set_of_labels(labelset, model):
    output = []
    for i in range(1, string_interner.counter):
        if str(model.evaluate(z3.Select(labelset, i))) == 'True': # bleh
            thing = string_interner.get_str(i)
            if "label_" in thing:
                output.append(thing[6:])
    return output
