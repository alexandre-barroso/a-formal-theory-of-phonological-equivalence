#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

{
  printf '%s\n' reports/SOURCE_MANIFEST.sha256
  find logs -type f -name '*.txt' -print
} | LC_ALL=C sort -u | while IFS= read -r file; do
  digest=$(shasum -a 256 "$file" | awk '{print $1}')
  printf '%s  %s\n' "$digest" "$file"
done > reports/ARTIFACT_MANIFEST.sha256
