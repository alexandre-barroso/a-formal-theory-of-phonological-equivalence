from __future__ import annotations

from fractions import Fraction

from .core import (ABSENT, And, Const, Decl, Feat, Made, Not, NodeId, Or_,
                   Present, RelDecl, SameFeat, Scope, Sigma, Slot, SortDecl,
                   Struct, TRUE, UNSCOPED, read)

_RAW = {
    "p": ("lab", False), "b": ("lab", True),
    "t": ("cor", False), "d": ("cor", True),
    "k": ("vel", False), "g": ("vel", True),
}
VOWEL = "i"


def make_sigma() -> Sigma:
    feats = {}
    for seg, (place, voi) in _RAW.items():
        feats[seg] = {"present": True, "obstruent": True, "place": place,
                      "voice": voi, "nuclear": False}
    feats[VOWEL] = {"present": True, "obstruent": False, "place": "undefined",
                    "voice": "undefined", "nuclear": True}
    feats[ABSENT] = {"present": False, "obstruent": "undefined",
                     "place": "undefined", "voice": "undefined",
                     "nuclear": "undefined"}
    default = {"present": True, "obstruent": False, "place": "undefined",
               "voice": "undefined", "nuclear": False}
    sorts = {"Or": SortDecl("Or", "total", tier="seg"),
             "Rel": SortDecl("Rel", "derived", tier="seg")}
    rels = {"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")}
    return Sigma(sorts=sorts, relations=rels, features=feats,
                 default_features=default, domains=("word", "morph"))


WORD = Scope(same=("word",), label="same_prosodic_word")
ANCHOR = Slot("t", "Or", "subject", kind="anchor")


def partner(policy="dynamic", filt=None, filter_mode="skip"):
    return Slot("n", "Rel", "subject", kind="step", relation="succ",
                scope=WORD, direction=+1, filter=filt, policy=policy,
                filter_mode=filter_mode)


def agree(policy="dynamic", filt=None, filter_mode="skip"):
    n = partner(policy, filt, filter_mode)
    return Decl("AGREE", "Or", (ANCHOR, n),
                And((Feat("obstruent", "t", True), Feat("obstruent", "n", True))),
                SameFeat("voice", ("t", "current"), ("n", "current")),
                scope=WORD)


def nogem(policy="dynamic", filt=None, filter_mode="skip"):
    n = partner(policy, filt, filter_mode)
    return Decl("NOGEM", "Or", (ANCHOR, n),
                And((Feat("obstruent", "t", True), Feat("obstruent", "n", True),
                     SameFeat("place", ("t", "current"), ("n", "current")))),
                Not(SameFeat("voice", ("t", "current"), ("n", "current"))),
                scope=WORD)


SCHEMA_ORDER = ("IDENT_PREFIX", "IDENT_STEM", "DEP", "AGREE", "NOGEM")


def declarations(policy="dynamic", filt=None, filter_mode="skip"):
    ident_prefix = Decl(
        "IDENT_PREFIX", "Or", (ANCHOR,), _morph("t", 0),
        SameFeat("voice", ("t", "current"), ("t", "reference")),
        kind="faithfulness")
    ident_stem = Decl(
        "IDENT_STEM", "Or", (ANCHOR,), _morph("t", 1),
        SameFeat("voice", ("t", "current"), ("t", "reference")),
        kind="faithfulness")
    dep = Decl("DEP", "Or", (ANCHOR,), Made("t"), Not(Present("t")),
               kind="faithfulness")
    return {"IDENT_PREFIX": ident_prefix, "IDENT_STEM": ident_stem, "DEP": dep,
            "AGREE": agree(policy, filt, filter_mode),
            "NOGEM": nogem(policy, filt, filter_mode)}


from dataclasses import dataclass
from .core import Term, K


@dataclass(frozen=True)
class DomIs(Term):
    slot: str
    domain: str
    value: int

    def slots(self): return frozenset({self.slot})

    def eval(self, ctx) -> K:
        o = ctx.resolve(self.slot)
        if o is None:
            return None
        v = ctx.state.dom.get(o, {}).get(self.domain)
        return None if v is None else v == self.value

    def depth(self): return 1


def _morph(slot, value):
    return DomIs(slot, "morph", value)


PRODUCTS = {
    "ap-gauti":    ("p", "g", "auti",  "a"),
    "ap-berti":    ("p", "b", "erti",  "a"),
    "at-taiki:ti": ("t", "t", "aiki:ti", "a"),
}


def build(pid) -> tuple[Struct, list, str]:
    c1, c2, tail, head = PRODUCTS[pid]
    nodes, real, dom = [], {}, {}
    i = 0

    def add(seg, morph, kind="lex"):
        nonlocal i
        n = NodeId("Or", kind, i); i += 1
        nodes.append(n); real[n] = seg; dom[n] = {"word": 0, "morph": morph}
        return n

    add(head, 0)
    n1 = add(c1, 0)
    site = NodeId("Or", "made", 1000)
    nodes.append(site); real[site] = ABSENT; dom[site] = {"word": 0, "morph": 1}
    i += 1
    n2 = add(c2, 1)
    for ch in tail:
        add(ch, 1)
    ref = Struct(order={"seg": tuple(nodes)}, real=real, dom=dom)
    return ref, [n1, site, n2], head


def candidates(ref, marks):
    n1, site, n2 = marks
    out = []
    for x in (0, 1):
        for y in (0, 1):
            for z in (0, 1):
                real = dict(ref.real)
                real[n1] = _flip(ref.real[n1], x)
                real[n2] = _flip(ref.real[n2], y)
                real[site] = VOWEL if z else ABSENT
                out.append(((x, y, z), Struct(order=ref.order, real=real,
                                              dom=ref.dom, assoc=ref.assoc)))
    return out


def _flip(seg, bit):
    place, _ = _RAW[seg]
    for s, (p, v) in _RAW.items():
        if p == place and v == bool(bit):
            return s
    raise KeyError(seg)


def observe(sigma, s) -> str:
    return "".join(s.real[n] for n in s.nodes("seg")
                   if sigma.present(s.real[n]))
