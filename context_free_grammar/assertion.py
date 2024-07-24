from node import Node
import numpy as np


class Assertion:
    def __init__(self, grammar):
        self.grammar = grammar
        self.root = Node("S")
        self.leaves = [self.root]
    
    def expand(self):
        while self.leaves:
            leaf = self.leaves[0]
            if not leaf.is_leaf:
                print("Invalid leaf")
                exit()
            if leaf.value not in self.grammar:
                leaf.leaf_to_not()
                self.leaves.remove(leaf)
                continue
            rnd_idx = np.random.choice(len(self.grammar[leaf.value]["args"]), p=self.grammar[leaf.value]["chances"])
            args = self.grammar[leaf.value]["args"][rnd_idx]
            leaf.value = args[0]
            if len(args) > 1:
                left = Node(args[1])
                leaf.add_left(left)
                self.leaves.remove(leaf)
                self.leaves.append(left)
            if len(args) > 2:
                right = Node(args[2])
                leaf.add_right(right)
                self.leaves.append(right)

    def __str__(self):
        return self.root.__str__()
    
    def create_smt2_line(self):
        return "(assert (" + self.root.create_smt2_line() + "))"

