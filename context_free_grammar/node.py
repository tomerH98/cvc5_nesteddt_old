class Node:
    def __init__(self, value):
        self.value = value
        self.children = []
        self.is_leaf = True

    def add_children(self, children):
        self.children = children
        self.is_leaf = False
    
    def leaf_to_not(self):
        self.is_leaf = False

    def __str__(self, level=0, prefix=""):
        ret = " " * (level * 4) + prefix + self.value + "\n"
        for child in self.children:
            ret += child.__str__(level + 1, prefix)
        return ret
    
    def create_smt2_line(self):
        if self.children==[]:
            return self.value
        else:
            return "(" + " " + self.value +" " + " ".join([child.create_smt2_line() for child in self.children]) + ")"