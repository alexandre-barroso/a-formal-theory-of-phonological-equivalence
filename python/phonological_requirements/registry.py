from __future__ import annotations

from .core import Decl


def declaration_sets():
    from . import frag_gua as FG, frag_lith as FL, frag_redup, frag_schwa, interaction_typology
    out = []
    sg = FG.make_sigma(); sgl = FL.make_sigma(); sgr = frag_redup.make_sigma(); sgs = frag_schwa.make_sigma()
    out += [("gua typed", sg, FG.declarations("typed")), ("lith RR (dynamic)", sgl, FL.declarations()),
            ("lith RR (witness)", sgl, FL.declarations(policy="witness")), ("lith RR (reference)", sgl, FL.declarations(policy="reference")),
            ("redup", sgr, frag_redup.declarations()), ("redup (foot_hl, superheavy, sync_listed)", sgr, frag_redup.declarations(exceptional="sync_listed", foot_hl=True, superheavy=True)),
            ("schwa", sgs, frag_schwa.declarations())]
    for name, pat in interaction_typology.PATTERNS.items():
        for mode in ("retain", "discharge", "ltr", "rtl"):
            sgq, D = interaction_typology.build_pattern(pat, (mode,) * len(pat["rules"]))
            out.append((f"seq:{name}:{mode}", sgq, D))
    for modname, fn in (("frag_stratal", "declarations"), ("frag_sandhi", "declarations"),
                        ("frag_nuer", "declarations"), ("frag_apocope", "declarations"),
                        ("frag_arapaho", "declarations"), ("frag_voice", "declarations"),
                        ("frag_morphaccent", "declarations")):
        mod = __import__(f"phonological_requirements.{modname}", fromlist=[fn])
        D = getattr(mod, fn)()
        sgm = mod.make_sigma() if hasattr(mod, "make_sigma") else mod.sigma()
        out.append((modname, sgm, D if isinstance(D, dict) else {d.name: d for d in D}))
    extra = {"frag_harmony": ("agree_pair", "block_after_high_initial", "spread_with_two_sided_block", "two_sided_height"),
             "frag_contact": ("ident_seg", "agree_voice", "ident_place"), "frag_antigem": ("syncope", "max_v", "ocp"),
             "frag_phase": ("tone_declarations", "melody_declarations"), "frag_accent": ("node_declarations", "feature_declarations"),
             "frag_abc": (), "frag_ocp": (), "frag_tn": (), "frag_turkish": (), "frag_auto": ()}
    for modname, builders in extra.items():
        mod = __import__(f"phonological_requirements.{modname}", fromlist=["x"])
        sgm = mod.make_sigma() if hasattr(mod, "make_sigma") else mod.sigma()
        D = {k: v for k, v in vars(mod).items() if isinstance(v, Decl)}
        for b in builders:
            r = getattr(mod, b)()
            if isinstance(r, dict): D.update(r)
            elif isinstance(r, Decl): D[r.name + ":" + b] = r
            else: D.update({d.name + ":" + b: d for d in r})
        if modname == "frag_contact":
            D["CONTACT_2"] = mod.contact_threshold(2); D["CONTACT_S1"] = mod.contact_stratum(1)
        out.append((modname + " (module-level)", sgm, D))
    from . import noninterference
    out.append(("t07 two-word", noninterference.make_sigma(noninterference.ALPHABET), noninterference.DECLS))
    if len({name for name, _, _ in out}) != len(out):
        raise ValueError("duplicate registered declaration-set name")
    for name, sigma, declarations in out:
        if sigma is None or not declarations:
            raise ValueError(f"incomplete registered declaration set: {name}")
    return out
