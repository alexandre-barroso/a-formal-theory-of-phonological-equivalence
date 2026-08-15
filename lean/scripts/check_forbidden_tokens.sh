#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
lean_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

if rg -n --glob '*.lean' --glob '!**/AxiomAudit.lean' \
    '\b(axiom|unsafe|sorry|admit|native_decide)\b' \
    "$lean_root/PhonologicalCalculus"; then
  printf '%s\n' 'FAIL: forbidden proof escape or project axiom found.' >&2
  exit 1
fi

printf '%s\n' 'PASS: no sorry, admit, native_decide, unsafe, or project axiom declarations found.'
