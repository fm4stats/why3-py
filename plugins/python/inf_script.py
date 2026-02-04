#!/usr/bin/env python3

import sys
import os
from pathlib import Path

from mypy import build
from mypy.options import Options
from mypy.traverser import TraverserVisitor
from mypy.nodes import OpExpr
from mypy.nodes import ComparisonExpr
from mypy.nodes import UnaryExpr
from mypy.types import Type

#print('foo', file=sys.stderr)

def type_of_node(types, node):
    if node not in types:
        return '?'
    ty = types[node]
    if not hasattr(ty, 'type'):
        return '?'
    return ty.type.name

def print_type(types, op, node, arg_nodes):
    arg_types = list(map(lambda n: type_of_node(types, n), arg_nodes))
    result_type = type_of_node(types, node)
    arg_types = ':'.join(arg_types)
    row = [
      str(node.line),
      str(node.column),
      str(node.end_line),
      str(node.end_column),
      op,
      arg_types,
      result_type
    ]
    print(','.join(row))

def analyse(filename):
    options = Options()
    #options.incremental = False
    options.preserve_asts = True
    options.export_types = True
    options.mypy_path = [os.path.dirname(filename)]

    python_code = Path(filename).read_text()
    mod, ext = os.path.splitext(os.path.basename(filename))

    result = build.build(sources=[build.BuildSource(filename, mod, python_code)], options=options)

    if result.errors:
        print("Errors:", result.errors)
        sys.exit(1)

    if mod not in result.graph:
        print(f"Error: {mod} module not found in result.graph")
        sys.exit(1)

    tree = result.graph[mod].tree
    types = result.types

    class ExpressionTypeExtractor(TraverserVisitor):
        def visit_op_expr(self, node: OpExpr) -> None:
            print_type(types, node.op, node, [node.left, node.right])
            super().visit_op_expr(node)

        def visit_comparison_expr(self, node: ComparisonExpr) -> None:
            left = node.operands[0]
            op = node.operators[0]
            right = node.operands[1]
            print_type(types, op, node, [left, right])
            super().visit_comparison_expr(node)

        def visit_unary_expr(self, node: UnaryExpr) -> None:
            print_type(types, node.op, node, [node.expr])
            super().visit_unary_expr(node)

    extractor = ExpressionTypeExtractor()
    tree.accept(extractor)

for fn in sys.argv[1:]:
    #print(fn, file=sys.stderr)
    analyse(fn)
