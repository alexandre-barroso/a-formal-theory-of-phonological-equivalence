from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from typing import Mapping

from phonological_opacity.fragments.gua import MARKEDNESS, GuaFragment, all_fragments, load_spec

from .adequacy import l_locus_terms, l_readers
from .gua_decls import (NEXT_WORD, PHRASE, SCHEMA_ORDER, agree_baseline,
                        agree_typed, declarations, signature_from_spec)
from .lang import Const, Declaration, Scope, Signature, read

VARIANTS: dict[str, dict] = {
    "baseline":            {"kind": "baseline"},
    "def_eq_context":      {"kind": "def_eq_context"},
    "def_eq_context_A":    {"kind": "def_eq_context", "schemas": ("A",)},
    "dynamic_next_word":   {"kind": "typed", "policy": "dynamic",
                            "scope": NEXT_WORD, "filter": None},
    "dynamic_phrase":      {"kind": "typed", "policy": "dynamic",
                            "scope": PHRASE, "filter": None},
    "dynamic_nucleus":     {"kind": "typed", "policy": "dynamic",
                            "scope": NEXT_WORD, "filter": "nuclear_nonhigh"},
    "dynamic_stop_nucleus": {"kind": "typed", "policy": "dynamic",
                             "scope": NEXT_WORD, "filter": "nuclear_nonhigh",
                             "filter_mode": "stop"},
    "origin_bound":        {"kind": "typed", "policy": "origin_bound",
                            "scope": NEXT_WORD, "filter": None},
    "witness":             {"kind": "typed", "policy": "witness",
                            "scope": NEXT_WORD, "filter": None},
    "witness_phrase":      {"kind": "typed", "policy": "witness",
                            "scope": PHRASE, "filter": None},
}


def build_declarations(name: str) -> dict[str, Declaration]:
    cfg = VARIANTS[name]
    if cfg["kind"] == "baseline":
        return declarations("baseline")
    if cfg["kind"] == "def_eq_context":
        base = declarations("baseline")
        out = dict(base)
        for k in cfg.get("schemas", MARKEDNESS):
            d = base[k]
            out[k] = Declaration(name=d.name, slots=d.slots,
                                 activation=d.activation,
                                 consequence=d.consequence, scope=d.scope,
                                 definedness_override=d.activation)
        return out
    kw = {k: v for k, v in cfg.items() if k in ("policy", "scope", "filter")}
    fm = cfg.get("filter_mode", "skip")
    a = agree_typed(**kw)
    slot = tuple(s if s.kind != "relatum" else
                 type(s)(s.name, s.kind, s.role, s.scope, s.direction,
                         s.filter, s.policy, fm) for s in a.slots)
    a = Declaration(name=a.name, slots=slot, activation=a.activation,
                    consequence=a.consequence, scope=a.scope)
    base = declarations("typed", policy=cfg["policy"])
    base["A"] = a
    return base


def score8(fragment: GuaFragment, sig: Signature,
           decls: Mapping[str, Declaration], state, ref_readers) -> int:
    terms = l_locus_terms(sig, fragment.reference, state, decls, ref_readers,
                          MARKEDNESS)
    total = Fraction(0)
    for name in SCHEMA_ORDER:
        old, new = terms[name]
        total += fragment.weights[name] * (Fraction(old) + fragment.lam * new)
    v = total * 8
    assert v.denominator == 1, v
    return int(v)


def evaluate_variant(name: str, spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    decls = build_declarations(name)
    out = {"variant": name, "inputs": {}, "well_typedness": {}}
    for k, d in decls.items():
        ok, faults = d.well_typed()
        out["well_typedness"][k] = {"well_typed": ok, "faults": list(faults),
                                    "relational_subject": d.relational()}
    for frag in all_fragments(spec):
        sig = signature_from_spec(spec, frag.record)
        ref = l_readers(sig, frag.reference, frag.reference, decls)
        values, obs = [], []
        for _i, cand in frag.all_candidates():
            values.append(score8(frag, sig, decls, cand, ref))
            obs.append(frag.observe(cand))
        target = frag.record["observation"]
        fiber = [i for i, y in enumerate(obs) if y == target]
        best = min(values)
        minima = [i for i, v in enumerate(values) if v == best]
        digest = hashlib.sha256(
            ",".join(str(v) for v in values).encode()).hexdigest()[:16]
        out["inputs"][frag.id] = {
            "states": frag.size,
            "minimum8": best,
            "minima": minima,
            "fiber": fiber,
            "exclusively_correct": bool(minima) and set(minima) <= set(fiber),
            "output_fibre_of_minima": sorted({obs[i] for i in minima}),
            "score_vector_sha256_16": digest,
            "values": values,
        }
    return out


def compare_all(spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    reports = {name: evaluate_variant(name, spec) for name in VARIANTS}
    base = reports["baseline"]
    summary = {}
    for name, rep in reports.items():
        rows = {}
        for uid, r in rep["inputs"].items():
            b = base["inputs"][uid]
            changed = [i for i, (x, y) in enumerate(zip(r["values"], b["values"]))
                       if x != y]
            rows[uid] = {
                "scores_identical": not changed,
                "changed_candidates": len(changed),
                "first_changed": changed[:5],
                "winners_identical": r["minima"] == b["minima"],
                "minima": r["minima"],
                "baseline_minima": b["minima"],
                "minimum8": r["minimum8"],
                "baseline_minimum8": b["minimum8"],
                "exclusively_correct": r["exclusively_correct"],
                "output_fibre_of_minima": r["output_fibre_of_minima"],
            }
        summary[name] = {
            "all_eight_exclusively_correct":
                all(v["exclusively_correct"] for v in rows.values()),
            "all_scores_identical_to_baseline":
                all(v["scores_identical"] for v in rows.values()),
            "all_winners_identical_to_baseline":
                all(v["winners_identical"] for v in rows.values()),
            "well_typed_A": rep["well_typedness"]["A"]["well_typed"],
            "A_faults": rep["well_typedness"]["A"]["faults"],
            "per_input": rows,
        }
    return summary


if __name__ == "__main__":
    print(json.dumps(compare_all(), ensure_ascii=False, indent=1))
