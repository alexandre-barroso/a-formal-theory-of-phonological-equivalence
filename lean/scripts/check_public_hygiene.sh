#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

volume_root="/Vol""umes/"
user_root="/Us""ers/"
private_root_pattern="${volume_root}|${user_root}"

if rg -n "$private_root_pattern" . \
    --glob '!.lake/**' --glob '!reports/*MANIFEST.sha256' \
    --glob '!scripts/check_public_hygiene.sh'; then
  printf '%s\n' 'FAIL: workstation-specific absolute path found.' >&2
  exit 1
fi

if test -d logs && find logs -type f -name '*.txt' -exec \
      perl -ne 'if (/[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]/) { print "$ARGV:$.:$_"; $bad=1 } END { exit($bad ? 0 : 1) }' \
      {} + | grep -q .; then
  printf '%s\n' 'FAIL: control character found in a public verification log.' >&2
  exit 1
fi

if test -f logs/leanchecker.txt && \
    rg -qi 'uncaught exception|could not find any oleans|(^|[^[:alpha:]])error:' \
      logs/leanchecker.txt; then
  printf '%s\n' 'FAIL: leanchecker log contains a failure diagnostic.' >&2
  exit 1
fi

printf '%s\n' 'PASS: no workstation-specific paths, log control characters, or leanchecker failure diagnostics found.'
