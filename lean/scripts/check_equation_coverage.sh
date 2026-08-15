#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
LABELS=$(mktemp)
TABLE_LABELS=$(mktemp)
TABLE_DECLS=$(mktemp)
AUDIT_LABELS=$(mktemp)
AUDIT_DECLS=$(mktemp)
trap 'rm -f "$LABELS" "$TABLE_LABELS" "$TABLE_DECLS" "$AUDIT_LABELS" "$AUDIT_DECLS"' EXIT HUP INT TERM

find "$ROOT/../proofs/shared/equations" -type f -name '*.tex' -print0 |
  xargs -0 grep -ho '\\label{eq:[^}]*}' |
  sed 's/^\\label{//; s/}$//' | LC_ALL=C sort > "$LABELS"

awk -F '\t' 'NR > 1 { print $1 }' "$ROOT/reports/equation_coverage.tsv" |
  LC_ALL=C sort > "$TABLE_LABELS"

sed -n 's/^-- \(eq:[^[:space:]]*\)$/\1/p' \
  "$ROOT/PhonologicalCalculus/EquationAudit.lean" | LC_ALL=C sort > "$AUDIT_LABELS"

count=$(wc -l < "$LABELS" | tr -d ' ')
[ "$count" -eq 63 ] || {
  echo "expected 63 public equation labels, found $count" >&2
  exit 1
}
[ "$(uniq -d "$LABELS" | wc -l | tr -d ' ')" -eq 0 ] || {
  echo "duplicate equation label in TeX sources" >&2
  uniq -d "$LABELS" >&2
  exit 1
}
[ "$(uniq -d "$TABLE_LABELS" | wc -l | tr -d ' ')" -eq 0 ] || {
  echo "duplicate equation label in equation_coverage.tsv" >&2
  uniq -d "$TABLE_LABELS" >&2
  exit 1
}

diff -u "$LABELS" "$TABLE_LABELS"
diff -u "$LABELS" "$AUDIT_LABELS"

awk -F '\t' 'NR == 1 {
    if ($1 != "equation_label" || $2 != "source_file" ||
        $3 != "lean_declarations" || $4 != "status" || $5 != "scope_note")
      exit 1
    next
  }
  NF != 5 || $1 == "" || $2 == "" || $3 == "" || $4 == "" || $5 == "" { exit 1 }
  END { if (NR != 64) exit 1 }
' "$ROOT/reports/equation_coverage.tsv" || {
  echo "malformed equation_coverage.tsv" >&2
  exit 1
}

awk -F '\t' 'NR > 1 {
  n = split($3, declaration, ";")
  for (i = 1; i <= n; i++) print declaration[i]
}' "$ROOT/reports/equation_coverage.tsv" | LC_ALL=C sort -u > "$TABLE_DECLS"

sed -n 's/^#check[[:space:]]\{1,\}\([^[:space:]]*\).*$/\1/p' \
  "$ROOT/PhonologicalCalculus/EquationAudit.lean" | LC_ALL=C sort -u > "$AUDIT_DECLS"

diff -u "$TABLE_DECLS" "$AUDIT_DECLS"

echo "PASS: 63 unique public equation labels have nonempty scoped Lean mappings."
