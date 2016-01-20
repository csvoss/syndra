class Node(object):
    def __init__(self):
        self.children = []
        pass
    def __init__(self, elt):
        self.children = []
        self.v = elt
    def addChild(self, elt):
        self.children.append(self)
