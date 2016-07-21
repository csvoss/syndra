"""
StringInterner and NodeInterner are utilities for keeping track of strings
paired to ints and nodes paired to strings.
"""

class StringInterner(object):
    """
    Store a set of strings, keying them to unique integers.
    Used by our solver to store labels in z3 as ints instead of strings.
    """
    def __init__(self):
        self._str_to_int = {}
        self._int_to_str = {}
        self.counter = 1

    def add(self, string):
        """Store a new string."""
        self._str_to_int[string] = self.counter
        self._int_to_str[self.counter] = string
        self.counter += 1

    def has_string(self, string):
        """Check if a string is stored."""
        return string in self._str_to_int

    def get_int(self, string):
        """Get the integer for a given string."""
        return self._str_to_int[string]

    def get_str(self, integer):
        """Get the string for a given integer."""
        return self._int_to_str[integer]

    def get_int_or_add(self, string):
        """Get the int for a given string, add it if not yet stored."""
        if not self.has_string(string):
            self.add(string)
        return self.get_int(string)


class NodeInterner(object):
    """
    Store a set of Node objects, keying them to unique strings.
    Used by our solver to ensure that each agent in a predicate gets assigned
    exactly one node. TODO: This may be redundant after nodes become enums.
    """
    def __init__(self, new_node_function):
        self._str_to_node = {}
        self._node_to_str = {}
        self.new_node_function = new_node_function

    def add(self, string, node):
        """Add a new string/node pair."""
        assert isinstance(string, str)
        self._str_to_node[string] = node
        self._node_to_str[node] = string

    def has_string(self, string):
        """Check if a string is stored."""
        assert isinstance(string, str)
        return string in self._str_to_node

    def get_node(self, string):
        """Get the node for a given string."""
        assert isinstance(string, str)
        return self._str_to_node[string]

    def get_str(self, node):
        """Get the string for a given node."""
        return self._node_to_str[node]

    def get_node_or_add(self, string):
        """Get the node for a given string, or add it if not yet noted."""
        assert isinstance(string, str)
        if not self.has_string(string):
            self.add(string, self.new_node_function(string))
        return self.get_node(string)
