from __future__ import annotations
from phonological_requirements import certificate, paths

import glob
import json
import re
import time
from fractions import Fraction as F
from pathlib import Path

from .core import Decl
from .registry import declaration_sets
from .strictness import atoms
from .syntax import atom_catalogue, encode

WS = paths.RESULTS
OUT = WS / "certificates"
SLOT_KINDS = ("anchor", "step", "stepof", "search", "assoc", "assocof", "corr")
POLICIES = ("dynamic", "dynamic_in_scope", "origin_bound", "witness", "reference")


def usage(sigma, D):
    u = {"slot_kinds": set(), "policies": set(), "filters": set(), "terms": set(), "kinds": set(), "locus_sides": set(),
         "scope_coords": set(), "definedness_override": False, "where_reference": False, "tiers": set(), "sort_classes": set()}
    for d in D.values():
        u["kinds"].add(d.kind); u["locus_sides"].add(d.locus_side)
        if d.definedness_override is not None: u["definedness_override"] = True
        for s in d.slots:
            u["slot_kinds"].add(s.kind)
            if s.kind != "anchor":
                u["policies"].add(s.policy)
                if s.filter: u["filters"].add(s.filter)
                if s.scope is not None: u["scope_coords"] |= set(s.scope.same) | set(s.scope.delta) | set(s.scope.min_delta)
                if getattr(s, "tier", None): u["tiers"].add(s.tier)
        for a in atoms(d.activation) + atoms(d.consequence):
            u["terms"].add(encode(a)[0])
            if getattr(a, "where", None) == "reference": u["where_reference"] = True
    for sd in sigma.sorts.values():
        u["sort_classes"].add(sd.totality)
    return u


def main():
    t0 = time.time()
    rec = {}
    sets = declaration_sets()
    ill = []
    for name, sigma, D in sets:
        for k, d in D.items():
            ok, why = d.well_typed(sigma)
            if not ok:
                ill.append((name, k, why))
    own_scoring, rival_scoring = [], []
    for f in sorted(glob.glob(str(paths.PACKAGE / "*.py"))):
        src = open(f).read(); base = Path(f).name
        if base in ("evaluate.py", "core.py"):
            continue
        if re.search(r"^def (score|coefficients|activation)\(", src, re.M):
            (own_scoring if base.startswith("frag_") else rival_scoring).append(base)
    fam = {}
    for name, _, D in sets:
        fam[name.split(":")[0].split(" ")[0]] = fam.get(name.split(":")[0].split(" ")[0], 0) + 1
    rec["a_specialisation"] = {"declaration_sets": len(sets), "sets_by_family": fam, "declarations": sum(len(D) for _, _, D in sets), "ill_typed": ill,
                               "fragment_modules_defining_their_own_scoring": own_scoring,
                               "runners_defining_a_scoring_function": rival_scoring,
                               "note": "a runner may implement a rival or a refutation with its own scoring (the schema-level activation bit); a fragment module never scores: every fragment is evaluated by gp.evaluate"}
    U = {name: usage(sigma, D) for name, sigma, D in sets}
    keys = ("slot_kinds", "policies", "filters", "terms", "kinds", "locus_sides", "scope_coords", "tiers", "sort_classes")
    shared = {k: sorted(set.intersection(*[U[n][k] for n in U])) for k in keys}
    union = {k: sorted(set.union(*[U[n][k] for n in U])) for k in keys}
    core_inventory = {"slot_kinds": set(SLOT_KINDS), "policies": set(POLICIES)}
    unused = {k: sorted(core_inventory[k] - set(union[k])) for k in core_inventory}
    per_set = {n: {k: sorted(v) if isinstance(v, set) else v for k, v in U[n].items()} for n in U}
    counts = {k: {v: sum(1 for n in U if v in U[n][k]) for v in union[k]} for k in keys}
    rec["b_usage"] = {"shared_by_every_set": shared, "used_by_some": union, "sets_using_each": counts, "core_primitives_unused": unused,
                      "sets_with_definedness_override": sorted(n for n in U if U[n]["definedness_override"]),
                      "sets_reading_the_reference": sorted(n for n in U if U[n]["where_reference"] or "reference" in U[n]["locus_sides"] or U[n]["policies"] & {"reference", "origin_bound", "witness"}),
                      "per_set": per_set}
    rec["predicate_catalogue"] = {
        "atom_constructors": sorted(name for name, _ in atom_catalogue().values()),
        "used_atom_constructors": sorted(union["terms"]),
        "logic_constructors": ["core.Const", "core.Not", "core.And", "core.Or_"],
        "scope": "The fixed catalogue includes predicates defined in fragment modules. It is not limited to the thirteen constructors in core.py."}
    formulae = [{"set": name, "declarations": [
        {"name": key, "activation": encode(d.activation), "consequence": encode(d.consequence)}
        for key, d in sorted(D.items())]} for name, _, D in sets]
    certificate.write("declaration_syntax.json", {"sets": formulae})
    g = json.load(open(OUT / "attenuation_region.json"))
    feas = {F(k): v for k, v in g["feasible"].items()}
    region = g["exact_region"]
    assert region["lower"] == "0" and region["upper"] == "1/2"
    assert region["lower_included"] and not region["upper_included"]
    fr = json.load(open(OUT / "schwa_attenuation.json"))
    lo, hi = fr["lambda_profile_interval_95"]
    common_lo, common_hi = max(0., lo), min(.5, hi)
    rec["c_common_domain"] = {"gua_exact_projection": {k: region[k] for k in ("lower", "upper", "lower_included", "upper_included")},
                              "french_profile_interval_95": [lo,hi],
                              "conditional_profile_intersection": {"lower":common_lo,"upper":common_hi,
                                  "lower_included":True,"upper_included":hi < .5},
                              "nonempty":common_lo < common_hi or (common_lo == common_hi and hi < .5),
                              "caveat":"The Gua projection is exact for the eight focal products with shared nonnegative weights. The French interval is a conditional aggregate likelihood profile, not a hard admissibility interval or evidence for cross-language parameter sharing."}
    rec["d_irreducible"] = [
        {"what": "the empirical sharing partition", "why": "pooled French contrasts and process/occasion-confounded Huai’an data do not identify whether sharing follows grammar, process, task or speaker", "proof": "conditional law and sampling design"},
        {"what": "the weights (a polytope per fragment)", "why": "two weight vectors inside a selecting region give identical outputs on every input of the productive schema", "proof": "D08.2"},
        {"what": "the resolution policy up to its two conditions", "why": "the surviving policies are score-identical on every declared product; the law selects by subject type and operation, not by data", "proof": "D03"},
        {"what": "the mode of a requirement", "why": "a formula of the consequence, fixed per requirement by the fate of its loci under destruction from each side", "proof": "D27.1, D27.5"},
        {"what": "an ordering asymmetry between two requirements", "why": "no mode and no attenuation supplies it; mutual counterfeeding stays generable", "proof": "D27.4, D27.7"},
    ]
    rec["shared_commitments"] = ["the sort table with total and derived sorts (origins against relation instances)", "the finite predicate library with strong-Kleene evaluation and Resolves total over a failing slot",
                                 "subject-strictness: the retained bit keyed per locus by the subject through t-correspondence", "activation read once off the fixed reference",
                                 "the retained construction's cells: w [a p + lambda (1 - a) p c]", "the four consequence modes as formulas", "additive weighting with one attenuation per grammar",
                                 "word- and phrase-scoped reading through the corrected footprint", "the finite reduction's closure as the candidate domain"]
    ok = bool(sets) and not ill and not own_scoring and bool(shared["slot_kinds"]) and bool(shared["sort_classes"])
    rec["all_pass"] = ok
    rec["status"] = "REGISTERED_SYNTAX_CHECKED" if ok else "FAILED"
    rec["scope"] = "Closed formulas and the static declaration checks. Source reconstruction, candidate preservation, full semantic translations and empirical explanation are separate obligations."
    rec["elapsed_s"] = round(time.time() - t0, 1)
    certificate.write("core_specialisation.json", rec)
    print("sets", len(sets), "declarations", rec["a_specialisation"]["declarations"], "ill-typed", len(ill), "own scoring", own_scoring)
    print("shared:", shared); print("counts (sets using):", {k: counts[k] for k in ("slot_kinds", "policies", "kinds", "locus_sides")})
    print("unused:", unused, "| conditional profile intersection:", rec["c_common_domain"]["conditional_profile_intersection"], rec["c_common_domain"]["nonempty"])
    print("status", rec["status"], rec["elapsed_s"], "s")
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
