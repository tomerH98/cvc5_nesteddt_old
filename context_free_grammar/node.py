class Node:
    def __init__(self, value):
        self.value = value
        self.right = None
        self.left = None
        self.is_leaf = True
    
    def add_left(self, left):
        self.left = left
        self.is_leaf = False
    
    def add_right(self, right):
        self.right = right
        self.is_leaf = False
    
    def leaf_to_not(self):
        self.is_leaf = False

    def __str__(self, level=0, prefix=""):
        ret = " " * (level * 4) + prefix + self.value + "\n"
        if self.left:
            ret += self.left.__str__(level + 1, "├── ")
        if self.right:
            ret += self.right.__str__(level + 1, "└── ")
        return ret
    
    def create_smt2_line(self):
        if self.right is None and self.left is None:
            return self.value
        left = self.left
        left_str = ""
        if left.left is None:
            left_str = left.create_smt2_line()
        else:
            left_str = "(" + left.create_smt2_line() + ")"
        if self.right is None:
            return self.value + " " + left_str
        right = self.right
        right_str = ""
        if right.left is None:
            right_str = right.create_smt2_line()
        else:
            right_str = "(" + right.create_smt2_line() + ")"
        return self.value + " " + left_str + " " + right_str