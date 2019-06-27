import ast


class IfNodeVisitor(ast.NodeTransformer):
    def __init__(self, model_variable_name: str,
                 predicate_model_name: bool = True):
        super().__init__()
        self.model_name = model_variable_name
        self.predicate_model_name = predicate_model_name

    def visit_If(self, node: ast.If):
        predicate = node.test
        # we only replace stuff if the predicate has something to do with the
        # verilog variable

        expression = node.body
        else_expression = node.orelse

        # recursive call
        for idx, node in enumerate(expression):
            if_exp = IfNodeVisitor(self.model_name, self.predicate_model_name)
            expression[idx] = if_exp.visit(node)
        for idx, node in enumerate(else_expression):
            else_exp = IfNodeVisitor(self.model_name, self.predicate_model_name)
            else_expression[idx] = else_exp.visit(node)

        if_node = ast.Call(func=ast.Attribute(value=ast.Name(id=self.model_name,
                                                             ctx=ast.Load()),
                                              attr="If",
                                              cts=ast.Load()),
                           args=[predicate] + expression,
                           keywords=[],
                           ctx=ast.Load)
        else_node = ast.Call(func=ast.Attribute(attr="Else", value=if_node,
                                                cts=ast.Load()),
                             args=else_expression, keywords=[])

        return ast.Expr(value=else_node)