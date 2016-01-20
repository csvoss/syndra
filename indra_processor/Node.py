class Node(object):
    def __init__(self):
        self.children = []
        pass
    def __init__(self, elt):
        self.children = []
        self.v = elt
    def addChild(self, elt):
        self.children.append(self)
    def repr(self):
        return str(self.v) + ''.join([str(c) for c in self.children])
