import ast


class IfNodeVisitor(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_If(self, node: ast.If):
        predicate = node.test
        # we only replace stuff if the predicate has something to do with the
        # verilog variable

        expression = node.body
        else_expression = node.orelse

        # recursive call
        for idx, node in enumerate(expression):
            if_exp = IfNodeVisitor()
            expression[idx] = if_exp.visit(node)
        for idx, node in enumerate(else_expression):
            else_exp = IfNodeVisitor()
            else_expression[idx] = else_exp.visit(node)

        if_node = ast.Call(func=ast.Attribute(value=ast.Name(id="self",
                                                             ctx=ast.Load()),
                                              attr="if_",
                                              cts=ast.Load()),
                           args=[predicate] + expression,
                           keywords=[],
                           ctx=ast.Load)
        else_node = ast.Call(func=ast.Attribute(attr="else_", value=if_node,
                                                cts=ast.Load()),
                             args=else_expression, keywords=[])

        return ast.Expr(value=else_node)


class AssignmentNodeVisitor(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_Assign(self, node: ast.Assign):
        pass


class TransformStatementList:
    def __init__(self):
        pass
