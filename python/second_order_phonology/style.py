from __future__ import annotations

import ast
import io
import tokenize
from pathlib import Path
from typing import Any

from .common import AuditOutputDirectory, ROOT, WriteJson, WriteTsv


def PythonFiles() -> list[Path]:
    return sorted(path for path in ROOT.rglob("*.py") if "build" not in path.parts and "release" not in path.parts and ".lake" not in path.parts)


def DocstringLines(tree: ast.AST) -> set[int]:
    lines: set[int] = set()
    nodes = [tree, *ast.walk(tree)]
    for node in nodes:
        body = getattr(node, "body", None)
        if isinstance(body, list) and body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            start = body[0].lineno
            end = getattr(body[0], "end_lineno", start)
            lines.update(range(start, end + 1))
    return lines


def PublicFunctionAnnotationFailures(tree: ast.AST) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) or node.name.startswith("_"):
            continue
        missing = []
        arguments = [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]
        if node.args.vararg is not None:
            arguments.append(node.args.vararg)
        if node.args.kwarg is not None:
            arguments.append(node.args.kwarg)
        for argument in arguments:
            if argument.arg not in {"self", "cls"} and argument.annotation is None:
                missing.append(argument.arg)
        if node.returns is None:
            missing.append("return")
        if missing:
            failures.append({"line": node.lineno, "function": node.name, "missing_annotations": ";".join(missing)})
    return failures


def ValidatePythonStyle() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    prohibited_markers = {"TO" + "DO", "FIX" + "ME", "X" * 3}
    for path in PythonFiles():
        relative = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        try:
            tree = ast.parse(text, filename=relative)
            syntax_status = "PASS"
        except SyntaxError as error:
            rows.append({"file": relative, "line": error.lineno or 0, "category": "syntax", "detail": error.msg})
            continue
        for token in tokenize.generate_tokens(io.StringIO(text).readline):
            if token.type == tokenize.COMMENT:
                rows.append({"file": relative, "line": token.start[0], "category": "comment", "detail": token.string})
        for line in sorted(DocstringLines(tree)):
            rows.append({"file": relative, "line": line, "category": "docstring", "detail": "string literal in docstring position"})
        for failure in PublicFunctionAnnotationFailures(tree):
            rows.append({"file": relative, "line": failure["line"], "category": "typing", "detail": f"{failure['function']}:{failure['missing_annotations']}"})
        for marker in prohibited_markers:
            if marker in text:
                rows.append({"file": relative, "line": 0, "category": "marker", "detail": marker})
        if syntax_status != "PASS":
            rows.append({"file": relative, "line": 0, "category": "syntax", "detail": syntax_status})
    status = "PASS" if not rows else "FAIL"
    report = {"status": status, "python_file_count": len(PythonFiles()), "finding_count": len(rows), "findings": rows}
    internal = AuditOutputDirectory()
    WriteJson(internal / "python_style_validation.json", report)
    WriteTsv(internal / "python_style_findings.tsv", rows, ["file", "line", "category", "detail"])
    return report
