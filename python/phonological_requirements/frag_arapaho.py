from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, InScope, Made, NodeId, Not, Or_,
                   Present, RelDecl, Resolves, SameFeat, SameSeg, Scope, Sigma,
                   Slot, SortDecl, Struct, TRUE)

V = dict(nuclear=True, dor=False, ant=False, glottal=False, son_top=False,
         cont=True, lab=False, nas=False, obs=False, present=True)
C = dict(nuclear=False, high=False, front=False, round=False, htone=False,
         glottal=False, present=True)


def _v(high, front, rnd, htone):
    return dict(V, high=high, front=front, round=rnd, htone=htone)


def _c(dor=False, ant=False, glottal=False, front=False, son_top=False,
       cont=False, lab=False, nas=False, obs=True):
    return dict(C, dor=dor, ant=ant, glottal=glottal, front=front,
                son_top=son_top, cont=cont, lab=lab, nas=nas, obs=obs)


FEATURES = {
    "e": _v(False, True, False, False), "é": _v(False, True, False, True),
    "o": _v(False, False, True, False), "ó": _v(False, False, True, True),
    "i": _v(True, True, False, False), "í": _v(True, True, False, True),
    "u": _v(True, False, True, False), "ú": _v(True, False, True, True),
    "b": _c(lab=True), "t": _c(ant=True), "tʃ": _c(),
    "k": _c(dor=True), "ʔ": _c(glottal=True),
    "θ": _c(ant=True, cont=True), "s": _c(ant=True, son_top=True, cont=True),
    "x": _c(dor=True, cont=True), "h": _c(glottal=True, cont=True),
    "n": _c(ant=True, nas=True, obs=False),
    "j": _c(front=True, cont=True, obs=False),
    "w": _c(dor=True, lab=True),
    ABSENT: dict(present=False, nuclear=None, high=None, front=None,
                 round=None, htone=None, dor=None, ant=None, glottal=None,
                 son_top=None, cont=None, lab=None, nas=None, obs=None),
}
IDENT_FEATURES = ("nuclear", "high", "front", "round", "htone", "dor",
                  "ant", "glottal", "cont", "lab", "nas", "obs")
ALPHABET = (ABSENT, "e", "é", "o", "ó", "i", "í", "u", "ú",
            "b", "t", "tʃ", "k", "ʔ", "θ", "s", "x", "h", "n", "j", "w")


def sigma() -> Sigma:
    return Sigma(
        sorts={"Or": SortDecl("Or", "total", tier="seg"),
               "Rel": SortDecl("Rel", "derived", tier="seg")},
        relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
        features=FEATURES,
        default_features=dict(present=True, nuclear=False, high=False,
                              front=False, round=False, htone=False,
                              dor=False, ant=False, glottal=False,
                              son_top=False, cont=False, lab=False,
                              nas=False, obs=False),
        domains=("word", "morph"))


WORD = Scope(same=("word",), label="word")
MORPH = Scope(same=("morph",), label="morph")
T = Slot("t", "Or", "subject", kind="anchor")
NXS = Slot("nx", "Or", "subject", kind="step", relation="succ", scope=WORD,
           direction=+1, policy="dynamic")
NXT = Slot("nx", "Or", "trigger", kind="step", relation="succ", scope=WORD,
           direction=+1, policy="dynamic")
def pv_slot(mode: str = "skip"):
    return Slot("pv", "Or", "trigger", kind="step", relation="succ",
                scope=WORD, direction=-1, filter="nuclear", filter_mode=mode,
                policy="dynamic")


PV = pv_slot("skip")
FV = Slot("fv", "Or", "trigger", kind="search", relation="succ", scope=WORD,
          direction=+1, filter="nuclear")


def _codaish():
    return And((Resolves("nx"), Feat("nuclear", "nx", False)))


def _front_trigger():
    return And((Resolves("nx"), Feat("front", "nx", True)))


def _epenthesis_site_front():
    return And((_codaish(), Resolves("pv"), Feat("round", "pv", False)))


def declarations(variant: str = "plain", pv_mode: str = "skip"):
    if variant not in ("plain", "duplicated", "lookahead", "no_trigger"):
        raise ValueError(variant)
    PV = pv_slot(pv_mode)
    if variant == "no_trigger":
        trig = TRUE
    elif variant == "plain":
        trig = _front_trigger()
    elif variant == "lookahead":
        trig = Or_((_front_trigger(),
                    And((_codaish(), Resolves("fv"), Feat("front", "fv", True)))))
    else:
        trig = Or_((_front_trigger(), _epenthesis_site_front()))
    slots = (T, NXT, PV) if variant != "lookahead" else (T, NXT, PV, FV)
    mut_dor = Decl("MUT_DOR", "Or", slots,
                   And((Feat("dor", "t", True), trig)),
                   Feat("dor", "t", False), scope=WORD)
    mut_ant = Decl("MUT_ANT", "Or", slots,
                   And((Feat("ant", "t", True), Feat("obs", "t", True),
                        Feat("son_top", "t", False),
                        Not(InScope("nx", MORPH, "t")), trig)),
                   Or_((Feat("ant", "t", False), Feat("son_top", "t", True))),
                   scope=WORD)
    nocoda = Decl("NOCODA", "Or", (T, NXS),
                  And((Feat("nuclear", "t", False),
                       Feat("glottal", "t", False))),
                  Or_((Feat("present", "t", False), Not(Resolves("nx")),
                       Feat("nuclear", "nx", True))),
                  scope=WORD)
    sync = Decl("SYNC", "Or", (T,),
                And((Feat("nuclear", "t", True), Feat("high", "t", True))),
                Or_((Feat("htone", "t", True), Feat("present", "t", False))),
                scope=WORD)
    dep = Decl("DEP", "Or", (T,), Made("t"),
               Or_((Not(Made("t")), Not(Present("t")))), kind="faithfulness")
    mx = Decl("MAX", "Or", (T,), Not(Made("t")), Present("t"),
              kind="faithfulness", locus_side="reference")
    ids = [Decl(f"ID_{f.upper()}", "Or", (T,), Not(Made("t")),
                SameFeat(f, ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")
           for f in IDENT_FEATURES]
    id_seg = Decl("ID_SEG", "Or", (T,), Not(Made("t")),
                  SameSeg(("t", "current"), ("t", "reference")),
                  kind="faithfulness", locus_side="reference")
    return {d.name: d for d in ([mut_dor, mut_ant, nocoda, sync, dep, mx,
                                 id_seg] + ids)}


def struct(segments, morphs=None, made=()):
    if morphs is None:
        morphs = [0] * len(segments)
    nodes, real, dom = [], {}, {}
    for i, v in enumerate(segments):
        n = NodeId("Or", "made" if i in made else "lex", i)
        nodes.append(n); real[n] = v; dom[n] = {"word": 0, "morph": morphs[i]}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom)


def eligible(s):
    return tuple(s.order["seg"])


CONFIGS = {
    "TRIG1": (["é", "tʃ", "e", "x", "í", "i", "h", "i", "ʔ"],
           [0, 0, 0, 0, 1, 1, 1, 1, 1]),
    "TRIG2": (["é", "k", "e", "t", "i", "i"],
           [0, 0, 1, 1, 1, 1]),
    "TRIG3": (["n", "ó", "ó", "h", "o", "w", "é", "θ", "e", "n"],
           [0, 0, 0, 0, 0, 0, 1, 1, 1, 1]),
    "CLUS1": (["é", "tʃ", "e", "x", "n", "ó", "w", "o", "ʔ"],
           [0, 0, 0, 0, 1, 1, 1, 1, 1]),
    "CLUS2": (["tʃ", "e", "w", "k", "ó", "ó", "h", "u"],
           [0, 0, 0, 1, 1, 1, 1, 1]),
    "CLUS3": (["n", "i", "h", "b", "e", "b", "í", "i", "θ", "t", "i", "i", "t"],
           [0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
    "RND1": (["w", "ó", "x", "h", "o", "o", "x"],
           [0, 0, 0, 0, 0, 0, 0]),
    "RND2": (["h", "o", "o", "w", "b", "é", "n"],
           [0, 0, 0, 0, 1, 1, 1]),
    "SUPP1": (["é", "tʃ", "e", "x", "i", "n", "ó", "w", "o", "ʔ"],
           [0, 0, 0, 0, 1, 2, 2, 2, 2, 2]),
    "SUPP2": (["n", "é", "í", "k", "i"], [0, 0, 0, 0, 1]),
    "SUPP3": (["b", "e", "x", "i"], [0, 0, 0, 1]),
    "SUPP4": (["b", "e", "b", "í", "i", "θ", "i", "t", "i", "i"],
           [0, 0, 0, 0, 0, 0, 1, 2, 2, 2]),
    "SUPP5": (["tʃ", "e", "w", "i", "k", "ó", "ó", "h", "u"],
           [0, 0, 0, 1, 2, 2, 2, 2, 2]),
    "MADE1": (["b", "e", "k", "u", "n", "o"],
           [0, 0, 0, 0, 0, 1]),
}


def config(name):
    segs, morphs = CONFIGS[name]
    return struct(segs, morphs)


LEX_TRIGGER = {"SUPP1": (4, 3), "SUPP2": (4, 3), "SUPP3": (3, 2), "SUPP4": (6, 5),
               "SUPP5": (3, 2)}
