#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/lean-axiom-script-tests.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT HUP INT TERM

cat > "$work_dir/targets.lean" <<'EOF'
#print axioms Test.alpha
#print axioms Test.beta
EOF

expect_failure() {
  label=$1
  log=$2
  if sh scripts/check_axiom_audit_output.sh \
      "$log" "$work_dir/targets.lean" >/dev/null 2>&1; then
    printf 'FAIL: negative axiom-audit test unexpectedly passed: %s\n' \
      "$label" >&2
    exit 1
  fi
}

printf '%s\n' 'sample.lean:1:0: error: unknown declaration Test.alpha' \
  > "$work_dir/error-only.log"
expect_failure error-only "$work_dir/error-only.log"

printf '%s\n' "'Test.alpha' does not depend on any axioms" \
  > "$work_dir/incomplete.log"
expect_failure incomplete "$work_dir/incomplete.log"

cat > "$work_dir/unexpected.log" <<'EOF'
'Test.alpha' does not depend on any axioms
'Test.beta' depends on axioms: [Classical.choice, Test.unsound]
EOF
expect_failure unexpected-axiom "$work_dir/unexpected.log"

cat > "$work_dir/valid.log" <<'EOF'
'Test.alpha' does not depend on any axioms
'Test.beta' depends on axioms: [Classical.choice, Quot.sound, propext]
EOF
sh scripts/check_axiom_audit_output.sh \
  "$work_dir/valid.log" "$work_dir/targets.lean" >/dev/null

printf '%s\n' \
  'PASS: axiom-audit checker rejects error-only, incomplete, and unexpected-axiom logs and accepts a complete whitelisted log.'
