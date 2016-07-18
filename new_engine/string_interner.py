from datatypes import new_node, Node

class StringInterner(object):

    def __init__(self):
        self._str_to_int = {}
        self._int_to_str = {}
        self.counter = 1

    def add(self, string):
        self._str_to_int[string] = self.counter
        self._int_to_str[self.counter] = string
        self.counter += 1

    def has_string(self, string):
        return string in self._str_to_int

    def get_int(self, string):
        return self._str_to_int[string]

    def get_str(self, integer):
        return self._int_to_str[integer]

    def get_int_or_add(self, string):
        if not self.has_string(string):
            self.add(string)
        return self.get_int(string)


string_interner = StringInterner()


class NodeInterner(object):

    def __init__(self):
        self._str_to_node = {}
        self._node_to_str = {}

    def add(self, string):
        assert isinstance(string, str)
        node = new_node(string)
        self._str_to_node[string] = node
        self._node_to_str[node] = string

    def has_string(self, string):
        assert isinstance(string, str)
        return string in self._str_to_node

    def get_node(self, string):
        assert isinstance(string, str)
        return self._str_to_node[string]

    def get_str(self, node):
        assert isinstance(node, Node), type(node)
        return self._node_to_str[node]

    def get_node_or_add(self, string):
        assert isinstance(string, str)
        if not self.has_string(string):
            self.add(string)
        return self.get_node(string)


node_interner = NodeInterner()
