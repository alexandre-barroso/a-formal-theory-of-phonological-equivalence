from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from typing import Mapping, Sequence

from phonological_opacity.fragments.gua import MARKEDNESS, SCHEMAS, GuaFragment, load_spec

from .adequacy import l_locus_terms, l_readers
from .gua_decls import SCHEMA_ORDER, signature_from_spec
from .variants import VARIANTS, build_declarations

P3_WEIGHTS = {"MAX": 9, "IDENT_ATR": 2, "IDENT_QUAL": 3, "IDENT_NUC": 4,
              "H": 8, "A": 12, "GL": 12, "D": 20, "INITIAL_FEATURE": 5}


def condition_holds(w: Mapping) -> bool:
    return w["MAX"] < min(w["IDENT_QUAL"] + w["IDENT_ATR"] + w["INITIAL_FEATURE"],
                          w["A"])


def make(spec: Mapping, reference_words: Sequence[Sequence[str]],
         phrases: Sequence[int], ident: str) -> GuaFragment:
    shim = dict(spec)
    rec = {"id": ident, "words": [list(x) for x in reference_words],
           "phrases": list(phrases),
           "focal": list(range(sum(len(x) for x in reference_words))),
           "observation": "", "source": "constructed locality stress case"}
    shim["inputs"] = list(spec["inputs"]) + [rec]
    return GuaFragment(shim, ident)


def _score(frag: GuaFragment, sig, decls, state, ref, weights, lam) -> Fraction:
    t = l_locus_terms(sig, frag.reference, state, decls, ref, MARKEDNESS)
    total = Fraction(0)
    for name in SCHEMA_ORDER:
        old, new = t[name]
        total += Fraction(weights[name]) * (Fraction(old) + lam * new)
    return total


def phrase_split(frag: GuaFragment) -> tuple[list[int], list[int]]:
    first = [q for q in range(frag.n) if frag.origins[q].phrase == 0]
    second = [q for q in range(frag.n) if frag.origins[q].phrase != 0]
    return first, second


def test_variant(spec: Mapping, variant: str, weights: Mapping, lam: Fraction,
                 reference_words, phrases, ident: str,
                 second_alphabet: Sequence[str] | None = None) -> dict:
    decls = build_declarations(variant)
    frag = make(spec, reference_words, phrases, ident)
    sig = signature_from_spec(spec, frag.record)
    ref = l_readers(sig, frag.reference, frag.reference, decls)
    first, second = phrase_split(frag)
    alphabet = list(spec["alphabet"])
    tail = list(second_alphabet) if second_alphabet is not None else alphabet
    ranges = [alphabet] + [tail] * (len(second) - 1) if second else []
    best_by_t: dict[tuple, tuple] = {}
    for t_vals in product(*ranges) if ranges else [()]:
        best, arg = None, []
        for s_vals in product(alphabet, repeat=len(first)):
            state = list(frag.reference)
            for q, v in zip(first, s_vals):
                state[q] = v
            for q, v in zip(second, t_vals):
                state[q] = v
            v = _score(frag, sig, decls, tuple(state), ref, weights, lam)
            if best is None or v < best:
                best, arg = v, [s_vals]
            elif v == best:
                arg.append(s_vals)
        best_by_t[t_vals] = (best, tuple(sorted(arg)))
    sets = {v[1] for v in best_by_t.values()}
    witness = None
    if len(sets) > 1:
        items = sorted(best_by_t.items(), key=lambda kv: str(kv[0]))
        first_set = items[0][1][1]
        for t_vals, (b, arg) in items:
            if arg != first_set:
                witness = {
                    "second_phrase_A": list(items[0][0]),
                    "first_phrase_minimisers_A": [list(x) for x in first_set],
                    "second_phrase_B": list(t_vals),
                    "first_phrase_minimisers_B": [list(x) for x in arg],
                }
                break
    return {
        "variant": variant,
        "reference": list(frag.reference),
        "phrases": list(phrases),
        "first_phrase_origins": first,
        "second_phrase_origins": second,
        "second_phrase_values_swept": len(best_by_t),
        "distinct_first_phrase_minimiser_sets": len(sets),
        "winner_level_phrase_local": len(sets) == 1,
        "witness": witness,
    }


def run(spec: Mapping | None = None, weights: Mapping | None = None,
        lam: Fraction | None = None,
        reference_words: Sequence[Sequence[str]] | None = None,
        phrases: Sequence[int] | None = None) -> dict:
    spec = spec or load_spec()
    weights = weights or P3_WEIGHTS
    lam = lam if lam is not None else Fraction(spec["lambda"]["num"],
                                               spec["lambda"]["den"])
    reference_words = reference_words or [["e"], ["\u0254"], ["e"], ["e"]]
    phrases = list(phrases) if phrases is not None else [0, 0, 1, 1]
    out = {
        "weights": dict(weights),
        "lambda": str(lam),
        "reference_words": [list(x) for x in reference_words],
        "phrases": list(phrases),
        "condition_w_MAX_lt_min": condition_holds(weights),
        "variants": {},
    }
    for variant in ("baseline", "dynamic_next_word", "dynamic_phrase",
                    "witness", "origin_bound", "def_eq_context"):
        out["variants"][variant] = test_variant(
            spec, variant, weights, lam, reference_words, phrases,
            f"winlocal_{variant}")
    return out


def sweep(spec: Mapping | None = None,
          variants: Sequence[str] = ("baseline", "dynamic_next_word", "witness"),
          weights: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    weights = weights or P3_WEIGHTS
    lam = Fraction(spec["lambda"]["num"], spec["lambda"]["den"])
    vowels = [v for v in ["a", "\u025c", "\u025b", "e", "\u026a", "i",
                          "\u0254", "o", "\u028a", "u"] if v in spec["alphabet"]]
    rows, hits, repaired_failures = [], 0, []
    for v0, v1 in product(vowels, repeat=2):
        if v0 == v1:
            continue
        words = [[v0], [v1], ["e"], ["e"]]
        res = {}
        for variant in variants:
            res[variant] = test_variant(spec, variant, weights, lam, words,
                                        [0, 0, 1, 1], f"sweep_{variant}",
                                        second_alphabet=["e"])
        row = {"first_phrase_reference": [v0, v1],
               "phrase_local": {k: v["winner_level_phrase_local"]
                                for k, v in res.items()},
               "baseline_witness": res["baseline"]["witness"]}
        if not res["baseline"]["winner_level_phrase_local"]:
            hits += 1
        for k, v in res.items():
            if k != "baseline" and not v["winner_level_phrase_local"]:
                repaired_failures.append({"reference": [v0, v1], "variant": k,
                                          "witness": v["witness"]})
        rows.append(row)
    return {"weights": dict(weights), "pairs_tried": len(rows),
            "sweep_note": ("the last second-phrase origin is held at its reference value e; "
                           "the first second-phrase origin ranges over the whole alphabet. "
                           "The headline configuration in 'single' is swept over the full "
                           "alphabet on both second-phrase origins."),
            "baseline_winner_level_failures": hits,
            "repaired_failures": repaired_failures,
            "rows": rows}


if __name__ == "__main__":
    print(json.dumps(run(), ensure_ascii=False, indent=1))
