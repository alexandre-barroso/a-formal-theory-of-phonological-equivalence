from __future__ import annotations

import sys

from .gua import GuaFragment, GuaProbe, load_spec as load_gua
from . import lithuanian as lit


def check_gua() -> list[str]:
    spec = load_gua()
    expected = spec["expected_regression"]["per_input"]
    failures: list[str] = []
    total = 0
    for record in spec["inputs"]:
        fragment = GuaFragment(spec, record["id"])
        got = fragment.evaluate()
        total += got["states"]
        want = expected[record["id"]]
        for key in ("states", "fiber", "minima", "minimum8"):
            if got[key] != want[key]:
                failures.append(f"gua/{record['id']}: {key} = {got[key]!r}, expected {want[key]!r}")
        if not got["exclusively_correct"]:
            failures.append(f"gua/{record['id']}: minimisers are not inside the correct fiber")
    if total != spec["expected_regression"]["total_candidates"]:
        failures.append(f"gua: {total} candidates, expected {spec['expected_regression']['total_candidates']}")
    return failures


def check_probe() -> list[str]:
    spec = load_gua()
    failures: list[str] = []
    for record in spec.get("probes", []):
        probe = GuaProbe(spec, record["id"])
        rows = probe.locus_report()
        want = record["expected"]
        for field in ("context", "defined", "good", "retained8"):
            got = [row[field] for row in rows]
            if got != want[field]:
                failures.append(f"probe/{record['id']}: {field} = {got!r}, expected {want[field]!r}")
        if want.get("first_phrase_projection_equal"):
            projections = {
                "".join(seg for seg, origin in zip(state, probe.origins)
                        if origin.phrase == 0 and probe.ft(seg)["present"])
                for state in probe.probe_states()
            }
            if len(projections) != 1:
                failures.append(f"probe/{record['id']}: first-phrase projections differ: {projections}")
    return failures


def check_lithuanian() -> list[str]:
    spec = lit.load_spec()
    weights, lam = lit.reference_weights(spec)
    expected = spec["expected_regression"]
    failures: list[str] = []
    for config in lit.CONFIGS:
        for record in spec["inputs"]:
            got = lit.evaluate(record, config, weights, lam)
            if got["fiber"] != expected["correct_fibers"][record["id"]]:
                failures.append(f"lt/{record['id']}: fiber = {got['fiber']!r}")
            pairs = (
                ("minimum8_at_reference_point", got["minimum8"]),
                ("minima_at_reference_point", got["minima"]),
                ("exclusively_correct_at_reference_point", got["exclusively_correct"]),
            )
            for key, value in pairs:
                want = expected[key][config][record["id"]]
                if value != want:
                    failures.append(f"lt/{config}/{record['id']}: {key} = {value!r}, expected {want!r}")
    return failures


def main() -> int:
    blocks = (("gua", check_gua), ("probe", check_probe), ("lithuanian", check_lithuanian))
    failures: list[str] = []
    for name, fn in blocks:
        found = fn()
        print(f"  {name}: {'PASS' if not found else f'FAIL ({len(found)})'}")
        failures.extend(found)
    for line in failures:
        print("    " + line, file=sys.stderr)
    print(f"  shared regression: {'PASS' if not failures else 'FAIL'}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
