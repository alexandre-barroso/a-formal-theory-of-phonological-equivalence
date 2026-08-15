#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

threads=${1:-${LEAN_BUILD_THREADS:-2}}
case "$threads" in
  ''|*[!0-9]*|0)
    printf 'Lean compiler thread count must be a positive integer (received: %s).\n' \
      "$threads" >&2
    exit 1
    ;;
esac

import_workers=${LEAN_IMPORT_WORKERS:-1}
case "$import_workers" in
  ''|*[!0-9]*|0)
    printf 'LEAN_IMPORT_WORKERS must be a positive integer (received: %s).\n' \
      "$import_workers" >&2
    exit 1
    ;;
esac
export LEAN_IMPORT_WORKERS="$import_workers"

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/lean-bounded-build.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT HUP INT TERM

{
  printf '%s\n' PhonologicalCalculus.lean
  find PhonologicalCalculus -type f -name '*.lean' -print
} | LC_ALL=C sort > "$work_dir/sources"

while IFS= read -r source; do
  module=$(printf '%s\n' "$source" | sed 's#/#.#g; s#\.lean$##')
  printf '%s %s\n' '__LEAN_BUILD_ROOT__' "$module"
  awk -v module="$module" \
    '/^import PhonologicalCalculus\./ { print $2, module }' "$source"
done < "$work_dir/sources" > "$work_dir/graph"

tsort "$work_dir/graph" |
  sed '/^__LEAN_BUILD_ROOT__$/d' > "$work_dir/order"

source_count=$(wc -l < "$work_dir/sources" | tr -d ' ')
module_count=$(wc -l < "$work_dir/order" | tr -d ' ')
if test "$source_count" -ne "$module_count"; then
  printf 'Bounded build graph mismatch: %s sources but %s modules.\n' \
    "$source_count" "$module_count" >&2
  exit 1
fi

override=$(printf 'weakLeanArgs=["-j%s"]' "$threads")
printf 'Bounded Lean build: %s modules; %s compiler threads; %s import worker(s).\n' \
  "$module_count" "$threads" "$import_workers"

index=0
while IFS= read -r module; do
  index=$((index + 1))
  printf '[%s/%s] %s\n' "$index" "$module_count" "$module"
  lake --no-ansi --log-level=warning -K "$override" build "+$module"
done < "$work_dir/order"

printf '%s\n' 'Bounded dependency-ordered Lean build completed successfully.'
