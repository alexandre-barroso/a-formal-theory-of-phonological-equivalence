#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
lean_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
deliverables_root=$(CDPATH= cd -- "$lean_root/.." && pwd)
overrides="$lean_root/reports/coverage_overrides.tsv"

awk -F '\t' 'BEGIN { OFS="\t" }
  NR==FNR { if (FNR>1 && $1=="result") { status[$2]=$3; decl[$2]=$4; note[$2]=$5 }; next }
  FNR==1 { print "result_id","group","formalization_status","lean_declaration","note_en"; next }
  {
    s=($1 in status ? status[$1] : "mapped_unformalized");
    d=($1 in decl ? decl[$1] : "");
    n=($1 in note ? note[$1] : "No exact Lean statement is provided in this bounded pass.");
    print $1,$2,s,d,n
  }' "$overrides" "$deliverables_root/registry/result_registry.tsv" \
  > "$lean_root/reports/result_coverage.tsv"

awk -F '\t' 'BEGIN { OFS="\t" }
  NR==FNR { if (FNR>1 && $1=="proof_goal") { status[$2]=$3; decl[$2]=$4; note[$2]=$5 }; next }
  FNR==1 { print "proof_goal_id","result_id","formalization_status","lean_declaration","note_en"; next }
  {
    s=($1 in status ? status[$1] : "mapped_unformalized");
    d=($1 in decl ? decl[$1] : "");
    n=($1 in note ? note[$1] : "No exact Lean statement is provided in this bounded pass.");
    print $1,$2,s,d,n
  }' "$overrides" "$deliverables_root/registry/proof_goal_registry.tsv" \
  > "$lean_root/reports/proof_goal_coverage.tsv"
