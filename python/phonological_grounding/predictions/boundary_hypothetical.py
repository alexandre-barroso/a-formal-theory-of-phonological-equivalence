from __future__ import annotations
from phonological_grounding.results import bare

import json
from fractions import Fraction
from pathlib import Path

from .boundary_sweep import check_point, region_points, weighted_score8
from .guaext import ConstructedInput, fragment

from .boundary_sweep import joint_rows
_ROWS: list | None = None


def JOINT_ROWS() -> list:
    global _ROWS
    if _ROWS is None:
        _ROWS = joint_rows()
    return _ROWS

HYPOTHETICAL_NOTE = (
    "HYPOTHETICAL, NOT SOURCE-LICENSED. Obiri-Yeboah & Rasin's Gua material "
    "contains one vowel-only word, the determiner 'a', and no sequence of two "
    "vowel-only words inside one phonological phrase. This input exists only to "
    "exhibit the configuration that the source-licensed pool excludes. It is "
    "not a Gua utterance and no claim about Gua rests on it.")

BIG_INIT = {"MAX": 20, "IDENT_ATR": 1, "IDENT_QUAL": 1, "IDENT_NUC": 2,
            "H": 4, "A": 8, "GL": 8, "D": 24, "INITIAL_FEATURE": 40}


def _build(first_of_phrase2: tuple[str, ...], tag: str) -> ConstructedInput:
    return ConstructedInput(
        id=f"HYP_{tag}",
        words=(("e",), ("ɔ",), first_of_phrase2, ("b", "ɛ")),
        phrases=(0, 0, 1, 1),
        focal=(0, 1, 2),
        note=HYPOTHETICAL_NOTE)


def winners_at(ci: ConstructedInput, w: dict[str, Fraction]) -> dict:
    f = fragment(ci)
    p1 = tuple(q for q in range(f.n) if f.origins[q].phrase == 0)
    best = None
    minima: list[int] = []
    for i in range(f.size):
        v = weighted_score8(f, f.candidate(i), w, Fraction(1, 8))
        if best is None or v < best:
            best, minima = v, [i]
        elif v == best:
            minima.append(i)
    proj = sorted({"".join(f.candidate(i)[q] for q in p1
                           if f.ft(f.candidate(i)[q])["present"]) for i in minima})
    return {"minimum": str(best), "n_minima": len(minima),
            "phrase1_projections": proj,
            "outputs": sorted({f.observe(f.candidate(i)) for i in minima})}


def run(out: Path | None = None) -> dict:
    pts = {k: v for k, v in region_points().items() if not check_point(v, JOINT_ROWS())}
    pts["big_init"] = {k: Fraction(v) for k, v in BIG_INIT.items()}
    admissible = {k: (not check_point(v, JOINT_ROWS())) for k, v in pts.items()}
    variants = {"phrase2_matches_e": ("e", "b", "ɪ"),
                "phrase2_differs_o": ("o", "b", "ɪ")}
    report: dict = {"note": HYPOTHETICAL_NOTE,
                    "point_admissibility": admissible,
                    "repair_condition":
                        "w_MAX < min(w_IDENT_QUAL + w_IDENT_ATR + w_INITIAL_FEATURE, w_A)",
                    "results": {}}
    for name, w in pts.items():
        block = {}
        for tag, third in variants.items():
            block[tag] = winners_at(_build(third, tag), w)
        block["phrase1_depends_on_phrase2"] = (
            block["phrase2_matches_e"]["phrase1_projections"]
            != block["phrase2_differs_o"]["phrase1_projections"])
        block["assimilation_cost"] = str(
            w["IDENT_QUAL"] + w["IDENT_ATR"] + w["INITIAL_FEATURE"])
        block["deletion_cost"] = str(w["MAX"])
        block["leave_A_violated_cost"] = str(w["A"])
        block["repair_condition_holds"] = (
            w["MAX"] < min(w["IDENT_QUAL"] + w["IDENT_ATR"] + w["INITIAL_FEATURE"], w["A"]))
        report["results"][name] = block
    if out:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(bare(report), indent=2, ensure_ascii=False))
    return report


if __name__ == "__main__":
    import sys
    o = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    r = run(o)
    for name, b in r["results"].items():
        print(f"{name:16s} admissible={r['point_admissibility'][name]} "
              f"MAX={b['deletion_cost']} assim={b['assimilation_cost']} "
              f"depends={b['phrase1_depends_on_phrase2']} "
              f"| matches {b['phrase2_matches_e']['phrase1_projections']} "
              f"differs {b['phrase2_differs_o']['phrase1_projections']}")
