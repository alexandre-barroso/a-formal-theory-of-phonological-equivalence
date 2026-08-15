#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

audit_file=${1:-logs/axiom_audit.txt}
target_file=${2:-PhonologicalCalculus/AxiomAudit.lean}
if test ! -s "$audit_file"; then
  printf 'FAIL: axiom-audit output is missing or empty: %s\n' "$audit_file" >&2
  exit 1
fi
if test ! -s "$target_file"; then
  printf 'FAIL: axiom-audit target file is missing or empty: %s\n' \
    "$target_file" >&2
  exit 1
fi
if grep -Eq '(^|[[:space:]])error:' "$audit_file"; then
  printf 'FAIL: Lean reported an error while producing the axiom audit: %s\n' \
    "$audit_file" >&2
  grep -E '(^|[[:space:]])error:' "$audit_file" >&2
  exit 1
fi

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/lean-axiom-policy.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT HUP INT TERM

rg --no-filename -o '^#print axioms [^[:space:]]+' "$target_file" |
  sed -E 's/^#print axioms //' |
  LC_ALL=C sort > "$work_dir/expected"

sed -n -E \
  "s/^'([^']+)' (does not depend on any axioms|depends on axioms:.*)$/\\1/p" \
  "$audit_file" |
  LC_ALL=C sort > "$work_dir/observed"

if LC_ALL=C uniq -d "$work_dir/observed" | grep -q .; then
  printf '%s\n' 'FAIL: duplicate successful axiom-audit response found.' >&2
  LC_ALL=C uniq -d "$work_dir/observed" >&2
  exit 1
fi

if ! cmp "$work_dir/expected" "$work_dir/observed" >/dev/null; then
  printf '%s\n' \
    'FAIL: the axiom-audit log does not contain one successful response per target.' >&2
  printf '%s\n' 'Targets missing a successful response:' >&2
  comm -23 "$work_dir/expected" "$work_dir/observed" >&2
  printf '%s\n' 'Successful responses without a target:' >&2
  comm -13 "$work_dir/expected" "$work_dir/observed" >&2
  exit 1
fi

awk '
  function emit(line, closes, count, idx, fields, value) {
    closes = (line ~ /]/)
    sub(/].*$/, "", line)
    count = split(line, fields, ",")
    for (idx = 1; idx <= count; idx++) {
      value = fields[idx]
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", value)
      if (value != "") print value
    }
    if (closes) collecting = 0
  }
  /depends on axioms:/ {
    line = $0
    sub(/^.*\[/, "", line)
    collecting = 1
    emit(line)
    next
  }
  collecting { emit($0) }
' "$audit_file" > "$work_dir/used-unsorted"
LC_ALL=C sort -u "$work_dir/used-unsorted" > "$work_dir/used"

printf '%s\n' Classical.choice Quot.sound propext |
  LC_ALL=C sort > "$work_dir/allowed"

comm -23 "$work_dir/used" "$work_dir/allowed" > "$work_dir/unexpected"
if test -s "$work_dir/unexpected"; then
  printf '%s\n' 'FAIL: unexpected axiom dependency found:' >&2
  cat "$work_dir/unexpected" >&2
  exit 1
fi

target_count=$(wc -l < "$work_dir/expected" | tr -d ' ')
axiom_count=$(wc -l < "$work_dir/used" | tr -d ' ')
printf 'PASS: all %s axiom-audit targets returned successfully; all %s reported axiom dependencies are in the explicit standard whitelist.\n' \
  "$target_count" "$axiom_count"
