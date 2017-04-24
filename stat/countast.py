import ast
from sys import argv

syntax_tree = ast.parse(open(argv[1]).read(), argv[1])

class V(ast.NodeVisitor):
    def __init__(self):
        self.total = 0
        self.depth = 0
        self.max = 0
        self.all_depth = []

    def visit_Name(self, node):
        print 'Name:', node.id
        self.generic_visit(node)

    def generic_visit(self, node):
        print type(node).__name__
        self.total += 1
        self.depth += 1
        current_total = self.total
        ast.NodeVisitor.generic_visit(self, node)
        if current_total == self.total:
            if self.depth > self.max:
                self.max = self.depth
            print self.depth
            self.all_depth.append(self.depth)
        self.depth -= 1

v = V()
v.visit(syntax_tree)
print v.total
print v.max
print sum(v.all_depth) * 1.0 / len(v.all_depth)

total = 0

for node in ast.walk(syntax_tree):
    break
    total += 1
    # print node

print total
# ast.dump(syntax_tree)