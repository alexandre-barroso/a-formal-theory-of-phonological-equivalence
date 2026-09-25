from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, NodeId, Not, Present, RelDecl,
                   Resolves, SameFeat, SameSeg, Scope, Sigma, Slot, SortDecl,
                   Struct, TRUE)

VOWELS = "aeiouəāēīōūáéíóúàèìòù"
CONS = {
    "p": ("lab", "stop", False, False), "b": ("lab", "stop", True, False),
    "f": ("lab", "fric", False, False), "v": ("lab", "fric", True, False),
    "m": ("lab", "nas", True, False), "w": ("lab", "glide", True, False),
    "t": ("cor", "stop", False, False), "d": ("cor", "stop", True, False),
    "ṭ": ("cor", "stop", False, True), "ḍ": ("cor", "stop", True, True),
    "s": ("cor", "fric", False, False), "z": ("cor", "fric", True, False),
    "ṣ": ("cor", "fric", False, True), "θ": ("cor", "fric", False, False),
    "ð": ("cor", "fric", True, False), "ʃ": ("pal", "fric", False, False),
    "c": ("pal", "stop", False, False), "n": ("cor", "nas", True, False),
    "l": ("cor", "liq", True, False), "r": ("cor", "liq", True, False),
    "y": ("pal", "glide", True, False), "k": ("dor", "stop", False, False),
    "g": ("dor", "stop", True, False), "q": ("uv", "stop", False, False),
    "x": ("dor", "fric", False, False), "X": ("dor", "fric", False, False),
    "ʔ": ("lar", "stop", False, False), "h": ("lar", "fric", False, False),
    "ʕ": ("phar", "fric", True, False), "ḥ": ("phar", "fric", False, False),
    "β": ("lab", "fric", True, False), "ŋ": ("dor", "nas", True, False),
    "j": ("pal", "stop", True, False),
    "ṃ": ("lab", "nas", True, True),
}


def features():
    f = {}
    for v in VOWELS:
        f[v] = dict(present=True, nuclear=True, weak=(v == "ə"), place=None,
                    manner=None, voice=None, cp=None)
    for c, (pl, mn, vc, cp) in CONS.items():
        f[c] = dict(present=True, nuclear=False, weak=False, place=pl, manner=mn,
                    voice=vc, cp=cp)
    f[ABSENT] = dict(present=False, nuclear=None, weak=None, place=None,
                     manner=None, voice=None, cp=None)
    return f


def sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=features(),
                 default_features=dict(present=True, nuclear=False, weak=False,
                                       place=None, manner=None, voice=None, cp=None),
                 domains=("word", "morph", "lexdom"))


def struct(segments, morphs, lexdoms=None):
    n = len(segments)
    lexdoms = lexdoms or [0] * n
    nodes = [NodeId("Or", "lex", i) for i in range(n)]
    real = {nd: s for nd, s in zip(nodes, segments)}
    dom = {nd: {"word": 0, "morph": morphs[i], "lexdom": lexdoms[i]} for i, nd in enumerate(nodes)}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom)


SCOPES = {"morph": Scope(same=("morph",), label="morph"),
          "lexdom": Scope(same=("lexdom",), label="lexdom"),
          "word": Scope(same=("word",), label="word")}
WORD = SCOPES["word"]
T = Slot("t", "Or", "subject", kind="anchor")
P = Slot("p", "Or", "trigger", kind="step", relation="succ", scope=WORD, direction=-1,
         policy="dynamic", filter="consonantal", filter_mode="stop")
N = Slot("n", "Or", "trigger", kind="step", relation="succ", scope=WORD, direction=+1,
         policy="dynamic", filter="consonantal", filter_mode="stop")
PP = Slot("pp", "Or", "trigger", kind="stepof", relation="succ", of="p", direction=-1,
          filter="nuclear", filter_mode="stop")
NN = Slot("nn", "Or", "trigger", kind="stepof", relation="succ", of="n", direction=+1,
          filter="nuclear", filter_mode="stop")


PV = Slot("pp", "Or", "trigger", kind="search", direction=-1, scope=WORD, filter="nuclear")


def syncope(left: str = "single") -> Decl:
    slots, act = [T], [Feat("weak", "t", True)]
    if left == "single":
        slots += [P, PP]; act += [Resolves("p"), Resolves("pp")]
    elif left == "cluster":
        slots += [PV]; act += [Resolves("pp")]
    elif left != "none":
        raise ValueError(left)
    slots += [N, NN]; act += [Resolves("n"), Resolves("nn")]
    return Decl("SYNCOPE", "Or", tuple(slots), And(tuple(act)), Not(Present("t")), scope=WORD)


def max_v() -> Decl:
    return Decl("MAX_V", "Or", (T,), Feat("nuclear", "t", True, where="reference"),
                Present("t"), kind="faithfulness", locus_side="reference")


def ocp(scope: str = "morph", identity="segment", adjacency="step") -> Decl:
    sc = SCOPES[scope]
    if adjacency == "step":
        nx = Slot("c", "Or", "subject", kind="step", relation="succ", scope=sc,
                  direction=+1, policy="dynamic", filter="consonantal", filter_mode="stop")
    else:
        nx = Slot("c", "Or", "subject", kind="search", direction=+1, scope=sc,
                  filter="consonantal")
    if identity == "segment":
        same = SameSeg(("t", "current"), ("c", "current"))
    else:
        same = And(tuple(SameFeat(f, ("t", "current"), ("c", "current")) for f in identity))
    name = f"OCP_{scope}_{adjacency}" + ("" if identity == "segment" else "_" + "+".join(identity))
    return Decl(name, "Or", (T, nx), And((Not(Feat("nuclear", "t", True)), Resolves("c"))),
                Not(same), scope=WORD)
