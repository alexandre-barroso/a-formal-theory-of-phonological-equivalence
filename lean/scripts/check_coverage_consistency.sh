#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/lean-coverage.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT HUP INT TERM

extract_registry_list() {
  list_name=$1
  awk -v list_name="$list_name" '
    $0 ~ ("^def " list_name " : List String := \\[") { active=1 }
    active {
      line=$0
      while (match(line, /"[^"]+"/)) {
        print substr(line, RSTART + 1, RLENGTH - 2)
        line=substr(line, RSTART + RLENGTH)
      }
    }
    active && /^]/ { exit }
  ' PhonologicalCalculus/Registry.lean | LC_ALL=C sort
}

extract_registry_list exactLeanResultIds > "$work_dir/exact-results"
extract_registry_list partialLeanResultIds > "$work_dir/partial-results"
extract_registry_list exactLeanProofGoalIds > "$work_dir/exact-proof_goals"

awk -F '\t' 'NR > 1 && $3 == "lean_closed" { print $1 }' \
  reports/result_coverage.tsv | LC_ALL=C sort > "$work_dir/report-exact-results"
awk -F '\t' 'NR > 1 && $3 == "partial_support_only" { print $1 }' \
  reports/result_coverage.tsv | LC_ALL=C sort > "$work_dir/report-partial-results"
awk -F '\t' 'NR > 1 && $3 == "lean_closed" { print $1 }' \
  reports/proof_goal_coverage.tsv | LC_ALL=C sort > "$work_dir/report-exact-proof_goals"

cmp "$work_dir/exact-results" "$work_dir/report-exact-results"
cmp "$work_dir/partial-results" "$work_dir/report-partial-results"
cmp "$work_dir/exact-proof_goals" "$work_dir/report-exact-proof_goals"

test "$(awk 'END { print NR - 1 }' reports/result_coverage.tsv)" -eq 68
test "$(awk 'END { print NR - 1 }' reports/proof_goal_coverage.tsv)" -eq 218

if awk -F '\t' 'NR > 1 { key=$1 FS $2; count[key]++ }
    END { for (key in count) if (count[key] != 1) print key }' \
    reports/coverage_overrides.tsv | grep -q .; then
  printf '%s\n' 'Duplicate coverage override found.' >&2
  exit 1
fi

while IFS= read -r result_id; do
  if awk -F '\t' -v result_id="$result_id" \
      'NR > 1 && $2 == result_id && $3 != "lean_closed" { found=1 }
       END { exit found ? 0 : 1 }' reports/proof_goal_coverage.tsv; then
    printf 'Incomplete proof-goal coverage for exact result %s.\n' \
      "$result_id" >&2
    exit 1
  fi
done < "$work_dir/exact-results"

printf '%s\n' \
  'PASS: Lean registry lists, row-level coverage, and 68/218 totals agree.'
