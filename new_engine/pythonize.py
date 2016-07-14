import z3

from datatypes import Rule, Graph, Edge
from string_interner import string_interner

def pythonized(pred, model):
    # Return a list of Rule objects
    # Apply the interpretation everywhere
    output = []
    interp = model[pred.interpretation_variable]
    rules = model[pred.model_variable].as_list()
    if type(rules[-1]) is not list:
        # For some reason the last element of 'rules' is usually True
        rules = rules[:-1]

    for pair in rules:
        rule, rule_in_model = pair[0], pair[1]
        assert rule_in_model # This says the rule is in the model
        output.append(RuleResult(rule, model, pred.interpretation_variable))

    return output


class RuleResult(object):
    def __init__(self, rule, model, interp_variable):
        pregraph = Rule.pregraph(rule)
        postgraph = Rule.postgraph(rule)
        self.pregraph = GraphResult(pregraph, model, interp_variable)
        self.postgraph = GraphResult(postgraph, model, interp_variable)

    def __repr__(self):
        return "Rule(%s -> %s)" % (str(self.pregraph), str(self.postgraph))


class GraphResult(object):
    def __init__(self, graph, model, interp_variable):
        ints_in_interp = [int(i) for i in str(model[interp_variable])[1:].replace('\n ', ' -> ').replace(', ', ' -> ').split(' -> ') if i.isdigit()]

        nodes = []

        has = Graph.has(graph)
        links = Graph.links(graph)
        parents = Graph.parents(graph)
        labelmap = Graph.labelmap(graph)

        agents = [j for i, j in string_interner._str_to_int.items() if 'label_' not in i]

        for value in agents:
            node_number = int(str(model.evaluate(interp_variable(value)))[5:-1])
            has_some_node = model.evaluate(z3.Select(has, interp_variable(value)))
            if has_some_node:
                try:
                    name = string_interner.get_str(value)
                except KeyError:
                    name = "NN#" + str(node_number)  # NN = no-name agent
                labels = model.evaluate(z3.Select(labelmap, interp_variable(value)))
                labels = labelset_to_set_of_labels(labels, model)
                nodes.append(NodeResult(value, name, labels))

        for node_1 in nodes:
            for node_2 in nodes:
                value_1 = node_1.value
                value_2 = node_2.value
                edge = Edge.edge(interp_variable(value_1), interp_variable(value_2))
                edge_in_parents = model.evaluate(z3.Select(parents, edge))
                edge_in_links = model.evaluate(z3.Select(links, edge))
                if str(edge_in_parents) == 'True':
                    node_1.add_site(node_2)
                if str(edge_in_links) == 'True':
                    node_1.add_link(node_2)

        self.nodes = nodes



        some_node = model.evaluate(interp_variable(1))
        has_some_node = model.evaluate(z3.Select(has, interp_variable(1)))

    def __repr__(self):
        return "{%s}" % (', '.join(str(node) for node in self.nodes))


class NodeResult(object):
    def __init__(self, value, name, labels):
        self.value = value
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
