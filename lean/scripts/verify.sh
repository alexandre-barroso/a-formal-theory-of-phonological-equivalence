#!/bin/sh
set -eu

if ! command -v lake >/dev/null 2>&1; then
  elan_bin=${ELAN_HOME:-"$HOME/.elan"}/bin
  if [ ! -x "$elan_bin/lake" ]; then
    printf '%s\n' 'Lean/Lake is unavailable; install Elan or add its bin directory to PATH.' >&2
    exit 1
  fi
  PATH=$elan_bin:$PATH
  export PATH
fi

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"
mkdir -p logs
find logs -maxdepth 1 -type f -name '*.txt' -delete
rm -f \
  reports/result_coverage.tsv \
  reports/proof_goal_coverage.tsv \
  reports/SOURCE_MANIFEST.sha256 \
  reports/ARTIFACT_MANIFEST.sha256

# Lean elaboration is memory-intensive for this aggregate.  Keep the public
# clean build bounded by default while permitting an explicit, reproducible
# override on larger hosts.
lean_build_threads=${LEAN_BUILD_THREADS:-${LEAN_BUILD_JOBS:-2}}
case "$lean_build_threads" in
  ''|*[!0-9]*|0)
    printf 'LEAN_BUILD_THREADS must be a positive integer (received: %s).\n' \
      "$lean_build_threads" >&2
    exit 1
    ;;
esac

{
  printf '%s\n' 'Lean toolchain'
  lake env lean --version
  printf '\n%s\n' 'Lake'
  lake --version
  printf '\n%s\n' 'Elan'
  elan --version
  printf '\n%s\n' 'Pinned toolchain'
  sed -n '1p' lean-toolchain
  printf '\n%s\n' 'Resolved mathlib revision'
  sed -n '/"name": "mathlib"/,/}/p' lake-manifest.json |
    sed -n 's/.*"rev": "\([^"]*\)".*/\1/p'
} > logs/versions.txt

{
  printf '%s\n' 'Pinned dependency resolution'
  printf '%s\n' 'lake-manifest.json is the authoritative resolved dependency lock.'
  printf '%s\n' 'No dependency update is performed during verification.'
  test -s lake-manifest.json
  grep -q '"name": "mathlib"' lake-manifest.json
  grep -q '"rev": "905b95818eb32af7874a58b427f50c1711a5e96c"' lake-manifest.json
  printf '%s\n' 'Pinned mathlib revision verified from the local lock file.'
} > logs/dependency_resolution.txt 2>&1

sh scripts/generate_registry_data.sh
sh scripts/generate_coverage_reports.sh
sh scripts/generate_mapping_audit.sh
sh scripts/generate_source_manifest.sh

{
  printf '%s\n' '$ sh scripts/check_forbidden_tokens.sh'
  sh scripts/check_forbidden_tokens.sh
} > logs/forbidden_tokens.txt 2>&1

{
  printf '%s\n' '$ sh scripts/check_coverage_consistency.sh'
  sh scripts/check_coverage_consistency.sh
} > logs/coverage_consistency.txt 2>&1

{
  printf '%s\n' '$ sh scripts/check_axiom_audit_coverage.sh'
  sh scripts/check_axiom_audit_coverage.sh
} > logs/axiom_audit_coverage.txt 2>&1

{
  printf '%s\n' '$ sh scripts/test_axiom_audit_scripts.sh'
  sh scripts/test_axiom_audit_scripts.sh
} > logs/axiom_audit_script_tests.txt 2>&1

{
  printf '%s\n' '$ sh scripts/check_equation_coverage.sh'
  sh scripts/check_equation_coverage.sh
} > logs/equation_coverage.txt 2>&1

{
  printf '%s\n' '$ lake clean phonological_calculus_lean'
  lake clean phonological_calculus_lean
  printf '\n$ sh scripts/build_bounded.sh %s\n' "$lean_build_threads"
  sh scripts/build_bounded.sh "$lean_build_threads"
  printf '\n%s\n' '$ lake --no-build build'
  lake --no-build build
} > logs/build.txt 2>&1

{
  printf '%s\n' '$ lake env lean PhonologicalCalculus/AxiomAudit.lean'
  lake env lean PhonologicalCalculus/AxiomAudit.lean
} > logs/axiom_audit.txt 2>&1

{
  printf '%s\n' '$ lake env lean PhonologicalCalculus/EquationAudit.lean'
  lake env lean PhonologicalCalculus/EquationAudit.lean
} > logs/equation_audit.txt 2>&1

{
  printf '%s\n' '$ lake env lean PhonologicalCalculus/MappingAudit.lean'
  lake env lean PhonologicalCalculus/MappingAudit.lean
} > logs/mapping_audit.txt 2>&1

{
  printf '%s\n' '$ sh scripts/check_axiom_audit_output.sh logs/axiom_audit.txt'
  sh scripts/check_axiom_audit_output.sh logs/axiom_audit.txt
} > logs/axiom_policy.txt 2>&1

{
  printf '%s\n' '$ lake env leanchecker --fresh PhonologicalCalculus.All'
  lake env leanchecker --fresh PhonologicalCalculus.All
} > logs/leanchecker.txt 2>&1

if rg -qi 'uncaught exception|could not find any oleans|(^|[^[:alpha:]])error:' \
    logs/leanchecker.txt; then
  printf '%s\n' 'FAIL: leanchecker emitted a failure diagnostic.' >> \
    logs/leanchecker.txt
  cat logs/leanchecker.txt >&2
  exit 1
fi
printf '%s\n' 'Independent kernel check completed successfully.' >> \
  logs/leanchecker.txt

{
  printf '%s\n' 'Result coverage'
  awk -F '\t' 'NR > 1 { count[$3]++ }
    END { for (status in count) print status "\t" count[status] }' \
    reports/result_coverage.tsv | sort
  printf '\n%s\n' 'Proof-goal coverage'
  awk -F '\t' 'NR > 1 { count[$3]++ }
    END { for (status in count) print status "\t" count[status] }' \
    reports/proof_goal_coverage.tsv | sort
  printf '\n%s\n' 'Registry totals'
  awk 'END { print "results\t" NR - 1 }' reports/result_coverage.tsv
  awk 'END { print "proof_goals\t" NR - 1 }' reports/proof_goal_coverage.tsv
} > logs/coverage_summary.txt

{
  printf '%s\n' '$ shasum -a 256 -c reports/SOURCE_MANIFEST.sha256'
  shasum -a 256 -c reports/SOURCE_MANIFEST.sha256
} > logs/source_manifest_check.txt 2>&1

{
  printf '%s\n' '$ sh scripts/check_public_hygiene.sh'
  sh scripts/check_public_hygiene.sh
} > logs/public_hygiene.txt 2>&1

sh scripts/generate_artifact_manifest.sh
