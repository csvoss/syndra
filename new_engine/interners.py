"""
StringInterner is a utility for keeping track of strings
paired to ints -- i.e., labels.
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
