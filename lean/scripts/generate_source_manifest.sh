#!/bin/sh
set -eu

lean_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$lean_root"

{
  find PhonologicalCalculus -type f -name '*.lean' -print
  find scripts -type f -print
  find reports -type f -name '*.tsv' -print
  printf '%s\n' \
    .gitignore \
    FOUNDATION.md \
    FOUNDATION.pt-BR.md \
    FORMALIZATION_MAP.md \
    FORMALIZATION_MAP.pt-BR.md \
    PhonologicalCalculus.lean \
    README.md \
    README.pt-BR.md \
    lake-manifest.json \
    lakefile.toml \
    lean-toolchain
} | LC_ALL=C sort -u | while IFS= read -r file; do
  digest=$(shasum -a 256 "$file" | awk '{print $1}')
  printf '%s  %s\n' "$digest" "$file"
done > reports/SOURCE_MANIFEST.sha256
