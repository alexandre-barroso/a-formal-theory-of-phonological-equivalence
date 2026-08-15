#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/lean-axiom-audit.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT HUP INT TERM

find PhonologicalCalculus -type f -name '*.lean' \
    ! -name AxiomAudit.lean -print |
  LC_ALL=C sort |
  while IFS= read -r source; do
    awk -f scripts/list_exported_theorems.awk "$source"
  done |
  LC_ALL=C sort > "$work_dir/declarations"

if LC_ALL=C uniq -d "$work_dir/declarations" | grep -q .; then
  printf '%s\n' 'FAIL: duplicate fully qualified exported declaration found.' >&2
  LC_ALL=C uniq -d "$work_dir/declarations" >&2
  exit 1
fi

rg --no-filename -o '^#print axioms [^[:space:]]+' \
  PhonologicalCalculus/AxiomAudit.lean |
  sed -E 's/^#print axioms //' |
  LC_ALL=C sort > "$work_dir/audited"

if LC_ALL=C uniq -d "$work_dir/audited" | grep -q .; then
  printf '%s\n' 'FAIL: duplicate fully qualified #print axioms target found.' >&2
  LC_ALL=C uniq -d "$work_dir/audited" >&2
  exit 1
fi

if ! cmp "$work_dir/declarations" "$work_dir/audited" >/dev/null; then
  printf '%s\n' 'FAIL: exported declarations and axiom-audit targets differ.' >&2
  printf '%s\n' 'Declarations missing from the audit:' >&2
  comm -23 "$work_dir/declarations" "$work_dir/audited" >&2
  printf '%s\n' 'Audit targets without an exported declaration:' >&2
  comm -13 "$work_dir/declarations" "$work_dir/audited" >&2
  exit 1
fi

count=$(wc -l < "$work_dir/declarations" | tr -d ' ')
printf 'PASS: all %s exported theorem and lemma declarations have one axiom-audit target.\n' \
  "$count"
