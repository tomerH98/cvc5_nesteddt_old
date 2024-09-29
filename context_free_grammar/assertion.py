from node import Node
import numpy as np


class Assertion:
    def __init__(self, grammar):
        self.grammar = grammar
        self.root = Node("S")
        self.leaves = [self.root]

    def expand(self):
        while self.leaves:
            leaf = self.leaves.pop(0)
            if leaf.value not in self.grammar or not leaf.is_leaf:
                leaf.leaf_to_not()
                continue
            rnd_idx = np.random.choice(len(self.grammar[leaf.value]["args"]),
                                       p=self.grammar[leaf.value]["chances"])
            args = self.grammar[leaf.value]["args"][rnd_idx]
            leaf.value = args[0]
            if len(args) > 1:
                children = []
                for arg in args[1:]:
                    child = Node(arg)
                    children.append(child)
                    self.leaves.append(child)
                leaf.add_children(children)
            else:
                self.leaves.append(leaf)

    def __str__(self):
        return self.root.__str__()

    def create_smt2_line(self):
        return "(assert " + self.root.create_smt2_line() + ")"
