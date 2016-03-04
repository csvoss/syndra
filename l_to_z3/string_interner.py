class StringInterner(object):

    def __init__(self):
        self.str_to_int = {}
        self.int_to_str = {}
        self.counter = 1

    def add(self, string):
        self.str_to_int[string] = self.counter
        self.int_to_str[self.counter] = string
        self.counter += 1

    def has_string(self, string):
        return string in self.str_to_int

    def get_int(self, string):
        return self.str_to_int[string]

    def get_str(self, integer):
        return self.int_to_str[integer]

    def get_int_or_add(self, string):
        if not self.has_string(string):
            self.add(string)
        return self.get_int(string)


string_interner = StringInterner()
