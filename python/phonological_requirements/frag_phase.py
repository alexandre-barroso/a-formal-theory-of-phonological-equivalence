from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, InScope, Linked, Made, NodeId, Not,
                   Or_, Positional, Present, RelDecl, Resolves, SameFeat, Scope,
                   Sigma, Slot, SortDecl, Struct, TRUE)

VOWELS = ("a", "e", "i", "o", "u", "ə", "O")
CONS = ("b", "d", "D", "g", "k", "l", "m", "n", "ñ", "s", "t", "tʃ", "j")
TONES = ("H", "L", "HL", "M")


def features():
    f = {}
    for v in VOWELS:
        for t in TONES:
            f[v + "_" + t] = dict(present=True, nuclear=True, tone=t,
                                  high_toned=(t in ("H", "HL")))
    for c in CONS:
        f[c] = dict(present=True, nuclear=False, tone=None, high_toned=False)
    f["HL"] = dict(present=True, nuclear=False, tone="HL", high_toned=True)
    f["L"] = dict(present=True, nuclear=False, tone="L", high_toned=False)
    f[ABSENT] = dict(present=False, nuclear=None, tone=None, high_toned=None)
    return f


def sigma() -> Sigma:
    return Sigma(
        sorts={"Or": SortDecl("Or", "total", tier="seg"),
               "Mel": SortDecl("Mel", "total", tier="mel",
                               comment="a lexically supplied floating melody"),
               "Rel": SortDecl("Rel", "derived", tier="seg")},
        relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel"),
                   "assoc": RelDecl("assoc", "association", "Mel", "Or", "Rel")},
        features=features(),
        default_features=dict(present=True, nuclear=False, tone=None, high_toned=False),
        domains=("word", "phrase", "morph", "aspect", "vdom"))


PHRASE = Scope(same=("phrase",), label="phrase")
T = Slot("t", "Or", "subject", kind="anchor")
PVT = Slot("p", "Or", "trigger", kind="step", relation="succ", scope=PHRASE,
           direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic")
VDOM = Scope(same=("vdom",), label="verb domain")
PVS = Slot("p", "Or", "subject", kind="step", relation="succ", scope=VDOM,
           direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic")
PVV = Slot("p", "Or", "trigger", kind="step", relation="succ", scope=VDOM,
           direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic")
TM = Slot("t", "Mel", "subject", kind="anchor")
HOST = Slot("h", "Or", "subject", kind="assoc", relation="assoc", tier="seg",
            where="current")


def tone_declarations():
    align = Decl("ALIGN_H_L", "Or", (T, PVS),
                 And((Feat("nuclear", "t", True), Feat("high_toned", "t", True),
                      _AspectIs("t", 1))),
                 Not(Resolves("p")), scope=PHRASE)
    need_h = Decl("NEED_H", "Or", (T, PVV),
                  And((Feat("nuclear", "t", True), Not(Resolves("p")),
                       _AspectIs("t", 1))),
                  Feat("high_toned", "t", True), scope=PHRASE)
    star_h = Decl("STAR_H", "Or", (T,), Feat("nuclear", "t", True),
                  Not(Feat("high_toned", "t", True)), scope=PHRASE)
    id_tone = Decl("ID_TONE", "Or", (T,), Not(Made("t")),
                   SameFeat("tone", ("t", "current"), ("t", "reference")),
                   kind="faithfulness", locus_side="reference")
    return {d.name: d for d in (align, need_h, star_h, id_tone)}


class _AspectIs:
    def __init__(self, slot, value):
        self.slot, self.value = slot, value
    def slots(self):
        return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None:
            return None
        return ctx.state.dom.get(o, {}).get("aspect") == self.value
    def depth(self):
        return 1


class _LinkedIntoWord:
    def __init__(self, slot, delta):
        self.slot, self.delta = slot, delta
    def slots(self):
        return frozenset({self.slot})
    def eval(self, ctx):
        m = ctx.resolve(self.slot)
        if m is None:
            return None
        w = ctx.state.dom[m]["word"] + self.delta
        return any(a == m and ctx.state.dom.get(b, {}).get("word") == w
                   for (a, b) in ctx.state.assoc)
    def depth(self):
        return 1


def melody_declarations(left_target: str = "word"):
    dock_hl_r = Decl("DOCK_HL_R", "Mel", (TM,),
                     And((Present("t"), Feat("tone", "t", "HL"))),
                     _LinkedIntoWord("t", +1))
    if left_target == "word":
        cons = _LinkedIntoWord("t", -1)
    else:
        cons = And((_LinkedIntoWord("t", -1), _LinkedIntoWord("t", -2)))
    dock_l_l = Decl("DOCK_L_L", "Mel", (TM,),
                    And((Present("t"), Feat("tone", "t", "L"))), cons)
    id_tone = Decl("ID_TONE", "Or", (T,), Not(Made("t")),
                   SameFeat("tone", ("t", "current"), ("t", "reference")),
                   kind="faithfulness", locus_side="reference")
    return {d.name: d for d in (dock_hl_r, dock_l_l, id_tone)}


def build(segs, words, morphs, phrase=0, aspect=0, melodies=(), vdom=None):
    nodes, real, dom = [], {}, {}
    for i, v in enumerate(segs):
        n = NodeId("Or", "lex", i)
        nodes.append(n); real[n] = v
        dom[n] = {"word": words[i], "morph": morphs[i], "phrase": phrase,
                  "aspect": aspect, "vdom": vdom[i] if vdom is not None else 0}
    mel = []
    for k, (val, w) in enumerate(melodies):
        m = NodeId("Mel", "lex", k)
        mel.append(m); real[m] = val
        dom[m] = {"word": w, "morph": -1, "phrase": phrase, "aspect": aspect, "vdom": 0}
    return Struct(order={"seg": tuple(nodes), "mel": tuple(mel)}, real=real, dom=dom)


def set_tone(s: Struct, node: NodeId, tone: str) -> Struct:
    base = s.real[node].split("_")[0]
    return s.with_real(node, base + "_" + tone)


def nuclei(s: Struct):
    sg = sigma()
    return [n for n in s.order["seg"] if sg.ft(s.real[n], "nuclear") is True]


def surface(s: Struct) -> str:
    marks = {"H": "́", "L": "̀", "HL": "̂", "M": ""}
    out, prev = [], None
    for n in s.order["seg"]:
        v = s.real[n]
        if prev is not None and s.dom[n]["word"] != s.dom[prev]["word"]:
            out.append(" ")
        if "_" in v:
            base, tone = v.split("_")
            out.append(base + marks[tone])
        else:
            out.append(v)
        prev = n
    return __import__("unicodedata").normalize("NFC", "".join(out))
