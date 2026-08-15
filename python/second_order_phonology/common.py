from __future__ import annotations

import csv
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[3]
GROUP_ORDER = {
    "CALC": 0,
    "FIN": 1,
    "CHG": 2,
    "CTX": 3,
    "FLUX": 4,
    "SUP": 5,
    "SEL": 6,
    "MAX": 7,
    "APP": 8,
    "DATA": 9,
}


def ReadJson(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def WriteJson(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)
    path.write_text(text + "\n", encoding="utf-8", newline="\n")


def ReadTsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def WriteTsv(path: Path, rows: Sequence[Mapping[str, Any]], fields: Sequence[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(fields), delimiter="\t", lineterminator="\n", extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow({field: NormalizeCell(row.get(field, "")) for field in fields})


def NormalizeCell(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    return str(value).replace("\t", " ").replace("\r", " ").replace("\n", " ")


def Sha256Bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def Sha256Text(value: str) -> str:
    return Sha256Bytes(value.encode("utf-8"))


def Sha256File(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def CatalogSortKey(identifier: str) -> tuple[int, int, str]:
    group = identifier.split("-", 1)[0]
    match = re.search(r"(\d+)$", identifier)
    number = int(match.group(1)) if match else -1
    return GROUP_ORDER.get(group, 99), number, identifier


def StripHoldComplete(value: str) -> str:
    match = re.fullmatch(r'HoldComplete\["(.*)"\]', value, flags=re.DOTALL)
    return match.group(1).replace('\\"', '"') if match else value


def TeXEscape(value: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(character, character) for character in value)


def MarkdownTable(rows: Sequence[Mapping[str, Any]], fields: Sequence[str]) -> str:
    header = "| " + " | ".join(fields) + " |"
    rule = "| " + " | ".join("---" for _ in fields) + " |"
    body = []
    for row in rows:
        body.append("| " + " | ".join(NormalizeCell(row.get(field, "")).replace("|", "\\|") for field in fields) + " |")
    return "\n".join([header, rule, *body]) + "\n"


def RelativePaths(paths: Iterable[Path]) -> list[str]:
    return [path.relative_to(ROOT).as_posix() for path in sorted(paths)]


def IgnoredDirectoryNames(root: Path = ROOT) -> set[str]:
    ignore_file = root / ".gitignore"
    if not ignore_file.is_file():
        return set()
    names: set[str] = set()
    for raw_line in ignore_file.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or line.startswith("!") or not line.endswith("/"):
            continue
        candidate = line.strip("/")
        if candidate and "/" not in candidate and not any(character in candidate for character in "*?[]"):
            names.add(candidate)
    return names


def AuditOutputDirectory(root: Path = ROOT) -> Path:
    generated_names = {"build", "__pycache__", ".pytest_cache", ".mypy_cache"}
    candidates = sorted(IgnoredDirectoryNames(root) - generated_names)
    if len(candidates) != 1:
        raise RuntimeError("The package must declare exactly one ignored audit-output directory")
    directory = root / candidates[0]
    directory.mkdir(parents=True, exist_ok=True)
    return directory
