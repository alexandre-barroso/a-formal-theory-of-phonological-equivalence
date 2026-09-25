from __future__ import annotations

import csv
import sys
from pathlib import Path

DATA = Path(__file__).resolve().parents[2] / "data" / "demonstrations"
RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def read(name: str) -> list[dict]:
    with open(DATA / name, encoding="utf-8") as fh:
        return list(csv.DictReader(fh, delimiter="\t"))


cells = read("portuguese_cells.tsv")
summary = read("portuguese_decision_summary.tsv")
check("demonstration: the Portuguese table has 72 rows", len(cells) == 72, str(len(cells)))
views = {(r["window_id"], r["band_lower_hz"]) for r in cells}
check("demonstration: the 72 rows are four readers over 18 views",
      len(views) == 18 and len({r["score_variant"] for r in cells}) == 4,
      f"{len(views)} views, {len({r['score_variant'] for r in cells})} variants")
check("demonstration: the natural row key (window, band, variant) is unique across the table",
      len({(r["window_id"], r["band_lower_hz"], r["score_variant"]) for r in cells}) == 72)
check("demonstration: all 72 medians are positive",
      all(float(r["median_delta"]) > 0 for r in cells),
      str([r["median_delta"] for r in cells if float(r["median_delta"]) <= 0][:3]))

strong = {}
for r in cells:
    strong[(r["window_id"], r["band_lower_hz"], r["score_variant"])] = r["development_gate_pass"] == "YES"
per_variant = {}
for (w, b, v), passed in strong.items():
    per_variant.setdefault(v, []).append(passed)
counts = {v: sum(vals) for v, vals in per_variant.items()}
check("demonstration: the strong gate passes 17/18 full, 11/18 leave-flatness-out, "
      "16/18 leave-high/low-out and 13/18 leave-zero-crossing-out",
      sorted(counts.values(), reverse=True) == [17, 16, 13, 11], str(counts))
check("demonstration: 57 of the 72 strong rows pass", sum(counts.values()) == 57, str(sum(counts.values())))

full = {(w, b): p for (w, b, v), p in strong.items() if v == "full"}
mismatches = [(w, b, v) for (w, b, v), p in strong.items() if v != "full" and p != full[(w, b)]]
yes_to_no = [m for m in mismatches if full[(m[0], m[1])]]
no_to_yes = [m for m in mismatches if not full[(m[0], m[1])]]
check("demonstration: the reductions produce 13 mismatch events relative to the full reader",
      len(mismatches) == 13, str(len(mismatches)))
check("demonstration: 12 are yes-to-no and one is no-to-yes",
      len(yes_to_no) == 12 and len(no_to_yes) == 1, f"{len(yes_to_no)}, {len(no_to_yes)}")
check("demonstration: the mismatches fall over nine distinct views",
      len({(m[0], m[1]) for m in mismatches}) == 9, str(len({(m[0], m[1]) for m in mismatches})))
check("demonstration: each cell rests on 14 matched comparisons",
      {int(r["n_inquiries"]) for r in cells} == {14}, str({r["n_inquiries"] for r in cells}))
numeric = [row for row in summary if row["strong_pass_cells"] != "not_applicable"]
union = next(row for row in summary if row["strong_pass_cells"] == "not_applicable")
check("data/demonstrations/portuguese_decision_summary.tsv agrees with the recomputed counts",
      all(int(row["strong_pass_cells"]) == counts[row["reader"]] for row in numeric)
      and all(int(row["strong_total_cells"]) == 18 for row in summary),
      str([(row["reader"], row["strong_pass_cells"]) for row in numeric]))
check("demonstration: the per-reader changed-decision counts 6, 3 and 4 sum to the 13 mismatch events",
      sum(int(row["changed_decisions_from_full"]) for row in numeric if row["reader"] != "full") == 13,
      str([(row["reader"], row["changed_decisions_from_full"]) for row in numeric]))
check("demonstration: the union of reduction witnesses covers nine distinct views",
      int(union["changed_decisions_from_full"]) == 9
      == len({(m[0], m[1]) for m in mismatches}), str(union))

agg = read("english_aggregate_cells.tsv")
margins = read("english_speaker_scenario_margins.tsv")
esum = read("english_decision_summary.tsv")[0]
check("demonstration: 300 aggregate scenario rows", len(agg) == 300, str(len(agg)))
check("demonstration: 150 scenarios over two splits",
      len({(r["tracker_id"], r["start_offset_ms"], r["end_offset_ms"]) for r in agg}) == 150
      and len({r["speaker_split"] for r in agg}) == 2)
check("demonstration: 14,135 speaker-scenario pairs", len(margins) == 14135, str(len(margins)))
median_fields = [f for f in agg[0] if f.endswith("_median_hz")]
check("demonstration: each aggregate row carries 14 median cells, giving 4,200 in total",
      len(median_fields) == 14 and len(agg) * len(median_fields) == 4200,
      f"{len(median_fields)} fields")
check("demonstration: all 4,200 median cells are positive",
      all(float(r[f]) > 0 for r in agg for f in median_fields))
check("demonstration: every aggregate row is DEFINED and reports the all-positive order",
      all(r["support_defined_n_ge_35"] == "DEFINED" for r in agg)
      and all(r["q_order_result"] == "DEFINED_ALL_14_POSITIVE" for r in agg))
check("demonstration: row identity distinguishes split, tracker and boundary pair",
      len({(r["speaker_split"], r["tracker_id"], r["start_offset_ms"], r["end_offset_ms"])
           for r in agg}) == 300)
check("data/demonstrations/english_decision_summary.tsv agrees with the recomputed counts",
      (int(esum["scenarios"]), int(esum["splits"]), int(esum["aggregate_rows"]),
       int(esum["positive_median_cells"]), int(esum["speaker_scenario_rows"]))
      == (150, 2, 300, 4200, 14135), str(esum))

rows = read("mandarin_rows.tsv")
msum = read("mandarin_decision_summary.tsv")
check("demonstration: the corrected Mandarin decision table has 639 rows", len(rows) == 639, str(len(rows)))
coarse = {"match": sum(r["original_decision"] == "MATCH" for r in rows),
          "counter": sum(r["original_decision"] == "COUNTEREXAMPLE" for r in rows),
          "refusal": sum(r["original_decision"] not in ("MATCH", "COUNTEREXAMPLE") for r in rows)}
fine = {"match": sum(r["corrected_decision"] == "MATCH" for r in rows),
        "counter": sum(r["corrected_decision"] == "COUNTEREXAMPLE" for r in rows),
        "refusal": sum(r["corrected_decision"] not in ("MATCH", "COUNTEREXAMPLE") for r in rows)}
published = {r["stage"]: r for r in msum}
check("demonstration: the coarse substring reader gives 621 matches, 18 counterexamples, 0 refusals",
      (coarse["match"], coarse["counter"], coarse["refusal"]) == (621, 18, 0), str(coarse))
check("demonstration: the construction-sensitive reader gives 622 matches, 13 counterexamples, 4 refusals",
      (fine["match"], fine["counter"], fine["refusal"]) == (622, 13, 4), str(fine))
check("demonstration: constructional scope corrects four clear cases and leaves four rows undefined",
      sum(1 for r in rows if r["original_decision"] == "COUNTEREXAMPLE"
          and r["corrected_decision"] == "MATCH") == 4 and fine["refusal"] == 4,
      str(sum(1 for r in rows if r["original_decision"] == "COUNTEREXAMPLE"
              and r["corrected_decision"] == "MATCH")))
check("demonstration: both stages partition the same 639 rows",
      sum(coarse.values()) == 639 == sum(fine.values()))
check("data/demonstrations/mandarin_decision_summary.tsv agrees with the recomputed counts",
      (int(published["coarse_substring"]["matches"]), int(published["coarse_substring"]["counterexamples"]),
       int(published["coarse_substring"]["refusals"])) == (621, 18, 0)
      and (int(published["construction_sensitive"]["matches"]),
           int(published["construction_sensitive"]["counterexamples"]),
           int(published["construction_sensitive"]["refusals"])) == (622, 13, 4)
      and int(published["construction_sensitive"]["clear_complex_final_retyped_as_match"]) == 4)


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} demonstration counts verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
