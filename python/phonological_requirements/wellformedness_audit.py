from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import time
from fractions import Fraction as F
from pathlib import Path

from .core import Const, Decl, NodeId, Slot, Struct
from .evaluate import activation, coefficients
from .generate import rename_created, canonical
from . import frag_gua as FG
from . import frag_lith as FL
from .products import gua_products

OUT = paths.CERTIFICATES


def wf_over(items):
    out = {}
    for label, sg, ref, cands in items:
        n = bad = 0
        first = None
        for c in cands:
            c = c[1] if isinstance(c, tuple) else c
            ok, faults = c.well_formed(ref)
            n += 1
            if not ok:
                bad += 1
                first = first or faults
        rok, rf = ref.well_formed(ref)
        out[label] = {"candidates": n, "ill_formed": bad, "first_fault": first, "reference_well_formed": rok}
    return out


def discipline_over(decl_sets):
    out = {}
    for label, sg, D in decl_sets:
        faults = {name: d.well_typed(sg)[1] for name, d in D.items() if not d.well_typed(sg)[0]}
        out[label] = {"declarations": len(D), "rejected": faults}
    return out


def lithuanian_s(kind: str):
    from .core import And, Feat, SameFeat, Not
    n = Slot("n", "Rel", "trigger", kind="step", relation="succ", scope=FL.WORD, direction=+1, policy="dynamic")
    n2 = Slot("n2", "Or", "subject", kind="step", relation="succ", scope=FL.WORD, direction=+1, policy="origin_bound")
    if kind == "AGREE":
        return Decl("AGREE", "Or", (FL.ANCHOR, n, n2),
                    And((Feat("obstruent", "t", True), Feat("obstruent", "n", True))),
                    SameFeat("voice", ("t", "current"), ("n2", "current")), scope=FL.WORD, definedness_override=Const(True))
    return Decl("NOGEM", "Or", (FL.ANCHOR, n, n2),
                And((Feat("obstruent", "t", True), Feat("obstruent", "n", True), SameFeat("place", ("t", "current"), ("n", "current")))),
                Not(SameFeat("voice", ("t", "current"), ("n2", "current"))), scope=FL.WORD, definedness_override=Const(True))


def main():
    t0 = time.time()
    rec = {}
    items = []
    sg = FG.make_sigma()
    for focal, prod in gua_products():
        ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        cands = []
        for combo in itertools.product(FG.ALPHABET, repeat=len(focal)):
            st = list(prod.reference)
            for q, v in zip(focal, combo):
                st[q] = v
            cands.append(FG.struct_from_segments(tuple(st), prod.words, prod.phrase_of_word))
        items.append((f"gua:{prod.id}", sg, ref, cands))
    sgl = FL.make_sigma()
    for pid in FL.PRODUCTS:
        ref, marks, _ = FL.build(pid)
        items.append((f"lith:{pid}", sgl, ref, list(FL.candidates(ref, marks))))
    from . import frag_seq, interaction_typology
    for name, pat in interaction_typology.PATTERNS.items():
        sgq = frag_seq.make_sigma(pat["alphabet"])
        for inp in pat["mappings"]:
            ref = frag_seq.build(interaction_typology.split(inp, pat["alphabet"]))
            items.append((f"seq:{name}:{inp}", sgq, ref, list(frag_seq.candidates(ref, pat["options"]))))
    from . import frag_redup, reduplication_template
    sgr = frag_redup.make_sigma()
    for it in reduplication_template.ITEMS[:12] + reduplication_template.ITEMS[13:16]:
        ref = frag_redup.build(it[1])
        items.append((f"redup:{it[0]}", sgr, ref, list(frag_redup.candidates(ref, it[1], **it[4]))))
    from . import frag_schwa, schwa_attenuation
    sgs = frag_schwa.make_sigma()
    for k, (label, syms, site, kind) in schwa_attenuation.CONTEXTS.items():
        ref = frag_schwa.build(syms, site, kind)
        items.append((f"schwa:{k}", sgs, ref, list(frag_schwa.candidates(ref, site, kind))))
    wf = wf_over(items)
    rec["well_formedness"] = wf
    tot = sum(v["candidates"] for v in wf.values()); bad = sum(v["ill_formed"] for v in wf.values())
    print(f"(a) well-formedness: {len(wf)} items, {tot} candidates, {bad} ill-formed")
    decl_sets = [("gua typed", sg, FG.declarations("typed")), ("lith RR (dynamic)", sgl, FL.declarations()),
                 ("lith RR (witness)", sgl, FL.declarations(policy="witness")), ("lith RR (reference)", sgl, FL.declarations(policy="reference")),
                 ("redup", sgr, frag_redup.declarations()), ("redup (foot_hl, superheavy, sync_listed)", sgr, frag_redup.declarations(exceptional="sync_listed", foot_hl=True, superheavy=True)),
                 ("schwa", sgs, frag_schwa.declarations())]
    for name, pat in list(interaction_typology.PATTERNS.items())[:6]:
        sgq, D = interaction_typology.build_pattern(pat, ("retain",) * len(pat["rules"]))
        decl_sets.append((f"seq:{name}", sgq, D))
        sgq, D = interaction_typology.build_pattern(pat, ("ltr",) * len(pat["rules"]))
        decl_sets.append((f"seq:{name}:ltr", sgq, D))
    for modname, fn in (("frag_stratal", "declarations"), ("frag_sandhi", "declarations"), ("frag_nuer", "declarations"), ("frag_apocope", "declarations"),
                        ("frag_harmony", "declarations"), ("frag_contact", "declarations"), ("frag_arapaho", "declarations"), ("frag_voice", "declarations"),
                        ("frag_abc", "declarations"), ("frag_ocp", "declarations"), ("frag_phase", "declarations"), ("frag_tn", "declarations"),
                        ("frag_turkish", "declarations"), ("frag_antigem", "declarations"), ("frag_accent", "declarations"), ("frag_morphaccent", "declarations"), ("frag_auto", "declarations")):
        try:
            mod = __import__(f"phonological_requirements.{modname}", fromlist=[fn])
            D = getattr(mod, fn)()
            sgm = mod.make_sigma() if hasattr(mod, "make_sigma") else (mod.sigma() if hasattr(mod, "sigma") else None)
            if sgm is None:
                continue
            decl_sets.append((modname, sgm, D if isinstance(D, dict) else {d.name: d for d in D}))
        except Exception as e:
            decl_sets.append((modname, None, {}))
            rec.setdefault("not_checked", {})[modname] = repr(e)[:120]
    from .core import Decl as _Decl
    extra = {"frag_harmony": ("agree_pair", "block_after_high_initial", "spread_with_two_sided_block", "two_sided_height"),
             "frag_contact": ("ident_seg", "agree_voice", "ident_place"), "frag_antigem": ("syncope", "max_v", "ocp"),
             "frag_phase": ("tone_declarations", "melody_declarations"), "frag_accent": ("node_declarations", "feature_declarations"),
             "frag_abc": (), "frag_ocp": (), "frag_tn": (), "frag_turkish": (), "frag_auto": ()}
    for modname, builders in extra.items():
        mod = __import__(f"phonological_requirements.{modname}", fromlist=["x"])
        sgm = mod.make_sigma() if hasattr(mod, "make_sigma") else (mod.sigma() if hasattr(mod, "sigma") else None)
        D = {k: v for k, v in vars(mod).items() if isinstance(v, _Decl)}
        for b in builders:
            r = getattr(mod, b)()
            if isinstance(r, dict): D.update(r)
            elif isinstance(r, _Decl): D[r.name + ":" + b] = r
            else: D.update({d.name + ":" + b: d for d in r})
        if modname == "frag_contact":
            D["CONTACT_2"] = mod.contact_threshold(2); D["CONTACT_S1"] = mod.contact_stratum(1)
        if sgm is not None and D:
            decl_sets.append((modname + " (all)", sgm, D))
            rec.setdefault("not_checked", {}).pop(modname, None)
    disc = {}
    for label, sgm, D in decl_sets:
        if sgm is None:
            continue
        disc[label] = discipline_over([(label, sgm, D)])[label]
    rec["discipline"] = disc
    nd = sum(v["declarations"] for v in disc.values()); nr = sum(len(v["rejected"]) for v in disc.values())
    print(f"(b) discipline: {len(disc)} declaration sets, {nd} declarations, {nr} rejected", {k: v["rejected"] for k, v in disc.items() if v["rejected"]})
    A = FG.agree_baseline()
    okA, fA = A.well_typed(sg)
    fact = {}
    for a in ("R", "S"):
        for b in ("R", "S"):
            D = FL.declarations()
            if a == "S": D["AGREE"] = lithuanian_s("AGREE")
            if b == "S": D["NOGEM"] = lithuanian_s("NOGEM")
            rej = {k: d.well_typed(sgl)[1] for k, d in D.items() if not d.well_typed(sgl)[0]}
            fact[a + b] = {"accepted": not rej, "rejected": rej}
    rec["proposition"] = {"gua_A_appendix": {"accepted": okA, "faults": list(fA)}, "gua_A_typed": {"accepted": FG.agree_typed().well_typed(sg)[0]},
                          "lithuanian_factorizations": fact,
                          "note": "the S readers are constructed as the appendix describes them (a relational trigger in the context, the same relatum as a surviving-origin subject in the consequence, a declared definedness); the appendix's own S declarations are in the dissertation's repository, not in this workspace"}
    print(f"(c) proposition: schema A rejected on {list(fA)}; factorizations accepted: {[k for k, v in fact.items() if v['accepted']]}")
    D = frag_redup.declarations(foot_hl=True, exceptional="dep_exempt")
    checked = mismatches = 0
    for it in reduplication_template.ITEMS[13:20]:
        ref = frag_redup.build(it[1]); acts = activation(sgr, ref, D)
        for c in frag_redup.candidates(ref, it[1]):
            made = [n.index for n in c.order["seg"] if n.kind == "made"]
            if not made:
                continue
            base = coefficients(sgr, ref, c, D, acts)
            for perm in ({i: 100 + i for i in made}, {i: j for i, j in zip(made, reversed(made))}):
                r = rename_created(c, perm)
                co = coefficients(sgr, ref, r, D, acts)
                checked += 1
                if co != base or canonical(r) != canonical(c):
                    mismatches += 1
    rec["renaming_equivariance"] = {"renamed_candidates": checked, "mismatches": mismatches}
    print(f"(d) renaming equivariance: {checked} renamed candidates, {mismatches} mismatches")
    from . import frag_apocope, apocope_counterfeeding, frag_morphaccent, morphological_accent
    eq = {}
    sga = frag_apocope.sigma()
    diff = n = 0
    for form in ("p á s o", "p á s o s", "k á s a", "p á s o s a"):
        segs = apocope_counterfeeding.parse(form); ref = frag_apocope.struct(segs); nodes = ref.order["seg"]
        Dn = {"CONTIG": frag_apocope.contig()}; Do = {"CONTIG": frag_apocope.contig_legacy()}
        an, ao = activation(sga, ref, Dn), activation(sga, ref, Do)
        dele = [i for i, sgm in enumerate(segs) if sgm not in "áéíóú"]
        for combo in itertools.product([0, 1], repeat=len(dele)):
            c = ref
            for i, k in zip(dele, combo):
                if k: c = c.with_real(nodes[i], frag_apocope.ABSENT if hasattr(frag_apocope, "ABSENT") else "∅")
            n += 1
            if coefficients(sga, ref, c, Dn, an)["CONTIG"] != coefficients(sga, ref, c, Do, ao)["CONTIG"]:
                diff += 1
    eq["CONTIG (apocope)"] = {"candidates": n, "differences": diff, "legacy_rejected": frag_apocope.contig_legacy().well_typed(sga)[1], "restated_accepted": frag_apocope.contig().well_typed(sga)[0]}
    sgm_ = frag_morphaccent.sigma()
    Dn = {"PSP": frag_morphaccent.declarations()["PSP"]}; Do = {"PSP": frag_morphaccent.psp_legacy()}
    diff = n = 0
    for items in (morphological_accent.ITEMS_JP, morphological_accent.ITEMS_RU, morphological_accent.ITEMS_CU):
        for name, morphs in items.items():
            ref = frag_morphaccent.build(morphs)
            an, ao = activation(sgm_, ref, Dn), activation(sgm_, ref, Do)
            for c in morphological_accent.candidates(ref):
                n += 1
                if coefficients(sgm_, ref, c, Dn, an)["PSP"] != coefficients(sgm_, ref, c, Do, ao)["PSP"]:
                    diff += 1
    eq["PSP (morphaccent)"] = {"candidates": n, "differences": diff, "legacy_rejected": frag_morphaccent.psp_legacy().well_typed(sgm_)[1], "restated_accepted": Dn["PSP"].well_typed(sgm_)[0]}
    rec["restatements"] = eq
    print("(e) restatements:", {k: (v["candidates"], v["differences"], v["restated_accepted"]) for k, v in eq.items()})
    rec["seconds"] = round(time.time() - t0, 1)
    certificate.write("wellformedness_audit.json", rec)
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main()
