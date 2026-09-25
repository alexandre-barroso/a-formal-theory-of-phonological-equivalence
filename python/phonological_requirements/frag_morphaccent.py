from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, InScope, Linked, Made, NodeId, Not,
                   Or_, Positional, Present, RelDecl, Resolves, Scope, Sigma,
                   Slot, SortDecl, Struct, TRUE)

SHORT = ("a", "e", "i", "o", "u", "ɨ", "ə")
LONG = ("aa", "ee", "ii", "oo", "uu", "ai", "au", "ei", "ou", "oi", "ie", "ea")
VOWELS = SHORT + LONG
MORAIC_CODA = "N"
FLAGS = ("dele", "delx", "prea", "preb", "shf", "exp")


def stressed(v: str) -> str:
    return v[0] + "\u0301" + v[1:]


def unstressed(v: str) -> str:
    return v.replace("́", "")


def features():
    f = {}
    for v in VOWELS:
        f[v] = dict(present=True, nuclear=True, moraic=True, long=v in LONG, stress=False)
        f[stressed(v)] = dict(present=True, nuclear=True, moraic=True, long=v in LONG, stress=True)
    f[MORAIC_CODA] = dict(present=True, nuclear=False, moraic=True, long=False, stress=False)
    f["A"] = dict(present=True, nuclear=False, moraic=False, long=False, stress=False)
    f[ABSENT] = dict(present=False, nuclear=None, moraic=None, long=None, stress=None)
    return f


def sigma() -> Sigma:
    sorts = {"Or": SortDecl("Or", "total", tier="seg"),
             "Rel": SortDecl("Rel", "derived", tier="seg"),
             "Acc": SortDecl("Acc", "total", tier="acc",
                             comment="a lexically supplied accent mark")}
    rels = {"succ": RelDecl("succ", "succession", "Or", "Or", "Rel"),
            "assoc": RelDecl("assoc", "association", "Acc", "Or", "Rel")}
    return Sigma(sorts=sorts, relations=rels, features=features(),
                 default_features=dict(present=True, nuclear=False, moraic=False,
                                       long=False, stress=False),
                 domains=("word", "syll", "morph", "rank", "side", "pwd") + FLAGS)


WORD = Scope(same=("word",), label="word")
SAME_MORPH = Scope(same=("morph",), label="same morph")
OUTER = Scope(same=("word",), min_delta={"rank": 1}, label="later-attached")

T = Slot("t", "Or", "subject", kind="anchor")
TA = Slot("t", "Acc", "subject", kind="anchor")
H = Slot("h", "Or", "subject", kind="assoc", relation="assoc", tier="seg",
         where="current")
HREF = Slot("hr", "Or", "subject", kind="assoc", relation="assoc", tier="seg",
            where="reference")
HREFT = Slot("hr", "Or", "trigger", kind="assoc", relation="assoc", tier="seg",
             where="reference")
AT = Slot("at", "Acc", "trigger", kind="assoc", relation="assoc", tier="acc")
PL = Slot("pl", "Or", "subject", kind="step", relation="succ", scope=WORD,
          direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic")
PLT = Slot("pl", "Or", "trigger", kind="step", relation="succ", scope=WORD,
           direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic")
NR = Slot("nr", "Or", "trigger", kind="step", relation="succ", scope=WORD,
          direction=+1, filter="nuclear", filter_mode="skip", policy="dynamic")
SL = Slot("l", "Or", "subject", kind="search", direction=-1, scope=WORD,
          filter="stressed")
SR = Slot("r", "Or", "subject", kind="search", direction=+1, scope=WORD,
          filter="stressed")
AL = Slot("al", "Acc", "subject", kind="assocof", of="l", relation="assoc",
          tier="acc", scope=WORD)
PINF = Slot("pinf", "Or", "subject", kind="step", relation="succ", scope=WORD,
            direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic",
            coord=(("side", 2),))
FINAL_NUC = Positional("last_live_of", "t", "word", "nuclear")
PWD = Scope(same=("word", "pwd"), label="prosodic word")
PL_PWD = Slot("pl", "Or", "subject", kind="step", relation="succ", scope=PWD,
              direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic")
NR_PWD = Slot("nr", "Or", "subject", kind="step", relation="succ", scope=PWD,
              direction=+1, filter="nuclear", filter_mode="skip", policy="dynamic")
PL_MORPH_T = Slot("pm", "Or", "trigger", kind="stepof", relation="succ", scope=SAME_MORPH,
                  direction=-1, filter="nuclear", filter_mode="skip", of="hr", tier="seg")
NR_PWD_H = Slot("hn", "Or", "subject", kind="stepof", relation="succ", scope=PWD,
                direction=+1, filter="nuclear", filter_mode="skip", of="h", tier="seg")


def outer(flag: str, name: str, direction: int, role: str = "trigger") -> Slot:
    return Slot(name, "Or", role, kind="search", of="hr", tier="seg",
                direction=direction, scope=OUTER, coord=((flag, 1),))


def adjacent(flag: str, name: str, direction: int) -> Slot:
    return Slot(name, "Or", "trigger", kind="step", relation="succ", scope=OUTER,
                direction=direction, filter="nuclear", filter_mode="skip",
                policy="dynamic", coord=((flag, 1),))


def adjacent_of(flag: str, name: str, direction: int) -> Slot:
    return Slot(name, "Or", "trigger", kind="stepof", relation="succ", scope=OUTER,
                direction=direction, filter="moraic", filter_mode="skip",
                coord=((flag, 1),), of="hr", tier="seg")


class _CoordIs:
    def __init__(self, slot, coord, value): self.slot, self.coord, self.value = slot, coord, value
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        v = ctx.state.dom[o].get(self.coord)
        if v is None: return None
        return v in self.value if isinstance(self.value, tuple) else v == self.value
    def depth(self): return 1


def st(slot: str):
    return Feat("stress", slot, True)


NUC = Feat("nuclear", "t", True)


def prosodic_declarations():
    culm = Decl("CULM", "Or", (T, SL, SR), st("t"),
                Or_((Not(st("t")), And((Not(Resolves("l")), Not(Resolves("r")))))),
                scope=WORD)
    head = Decl("HEAD", "Or", (T, PLT, SR), And((NUC, Not(Resolves("pl")))),
                Or_((st("t"), Resolves("r"))), scope=WORD)
    align_r = Decl("ALIGN_R", "Or", (T, SL, AL), NUC,
                   Or_((Not(Resolves("l")), Made("al"))), scope=WORD)
    align_r_all = Decl("ALIGN_R_ALL", "Or", (T, SL), NUC, Not(Resolves("l")),
                       scope=WORD)
    init = Decl("INIT", "Or", (T, AT, PL), And((st("t"), Resolves("at"), Made("at"))),
                Not(Resolves("pl")), scope=WORD)
    nonfinal = Decl("NONFINAL", "Or", (T,), st("t"),
                    Or_((Not(st("t")), Not(FINAL_NUC))), scope=WORD)
    align_r_pwd = Decl("ALIGN_R_PWD", "Or", (T, NR_PWD), st("t"),
                       Or_((Not(st("t")), Not(Resolves("nr")))), scope=WORD)
    align_l_pwd = Decl("ALIGN_L_PWD", "Or", (T, PL_PWD), st("t"),
                       Or_((Not(st("t")), Not(Resolves("pl")))), scope=WORD)
    psp = Decl("PSP", "Or", (T, PL), st("t"),
               Or_((Not(st("t")), And((_CoordIs("t", "side", 2), Resolves("pl"),
                                        Not(_CoordIs("pl", "side", 2)))))),
               scope=WORD)
    return {d.name: d for d in (culm, head, align_r, align_r_all, init, nonfinal, psp,
                                align_r_pwd, align_l_pwd)}


def faithfulness_declarations():
    out = {}
    for name, sides in (("MAX_R", (0,)), ("MAX_S", (1,)), ("MAX_A", (2,))):
        out[name] = Decl(name, "Acc", (TA,), _CoordIs("t", "side", sides), Present("t"),
                         kind="faithfulness", locus_side="reference")
    out["DEP"] = Decl("DEP", "Acc", (TA,), Made("t"),
                      Or_((Not(Made("t")), Not(Present("t")))), kind="faithfulness")
    for name, sides in (("MAXLINK_R", (0,)), ("MAXLINK_X", (1, 2))):
        out[name] = Decl(name, "Acc", (TA, HREF), _CoordIs("t", "side", sides),
                         Or_((Not(Present("t")), Linked("t", "hr", where="current"))),
                         kind="faithfulness", locus_side="reference")
    out["MAX_INIT"] = Decl("MAX_INIT", "Acc", (TA, HREFT, PL_MORPH_T),
                           And((_CoordIs("t", "side", (0,)), Not(Made("t")), Resolves("hr"),
                                Not(Resolves("pm")))),
                           Present("t"), kind="faithfulness", locus_side="reference")
    out["LOCAL"] = Decl("LOCAL", "Acc", (TA, H, HREFT),
                        And((Present("t"), Resolves("hr"), Resolves("h"))),
                        InScope("h", SAME_MORPH, "t"), kind="faithfulness",
                        locus_side="reference")
    return out


def _base_has(flag):
    return Or_((Resolves("dr"), Resolves("dl")))


def anti_declarations():
    out = {}
    lex = And((Not(Made("t")), Resolves("hr")))
    out["ANTI_DEL"] = Decl(
        "ANTI_DEL", "Acc", (TA, HREFT, outer("dele", "dr", +1), outer("dele", "dl", -1)),
        And((lex, _base_has("dele"))), Not(Present("t")),
        kind="faithfulness", locus_side="reference")
    out["ANTI_DEL_ADJ"] = Decl(
        "ANTI_DEL_ADJ", "Acc", (TA, HREFT, adjacent_of("delx", "dr", +1), adjacent_of("delx", "dl", -1)),
        And((lex, Not(Feat("long", "hr", True, where="reference")), _base_has("delx"))),
        Not(Present("t")), kind="faithfulness", locus_side="reference")
    dr, dl = outer("shf", "dr", +1, "subject"), outer("shf", "dl", -1, "subject")
    out["ANTI_SHIFT"] = Decl(
        "ANTI_SHIFT", "Acc", (TA, H, HREFT, NR_PWD_H, dr, dl), And((lex, _base_has("shf"))),
        And((Present("t"), Resolves("h"), Not(Resolves("hn")),
             Or_((And((Resolves("dr"), InScope("dr", OUTER, "h"))),
                  And((Resolves("dl"), InScope("dl", OUTER, "h"))))))),
        kind="faithfulness", locus_side="reference")
    dr, dl = outer("exp", "dr", +1, "subject"), outer("exp", "dl", -1, "subject")
    out["ANTI_EXPEL"] = Decl(
        "ANTI_EXPEL", "Acc", (TA, H, HREF, dr, dl), And((lex, _base_has("exp"))),
        Or_((Not(Present("t")),
             And((Resolves("dr"), Not(InScope("dr", OUTER, "h")))),
             And((Resolves("dl"), Not(InScope("dl", OUTER, "h")))))),
        kind="faithfulness", locus_side="reference")
    for flag, name in (("prea", "ANTI_PRE_A"), ("preb", "ANTI_PRE_B")):
        out[name] = Decl(name, "Or", (T, adjacent(flag, "nx", +1), adjacent(flag, "px", -1)),
                         Or_((Resolves("nx"), Resolves("px"))), st("t"), scope=WORD)
    return out


def psp_legacy() -> Decl:
    return Decl("PSP", "Or", (T, PL, PINF), st("t"),
                Or_((Not(st("t")), And((_CoordIs("t", "side", 2), Resolves("pl"),
                                         Not(Resolves("pinf")))))),
                scope=WORD)


def declarations():
    D = {}
    D.update(prosodic_declarations()); D.update(faithfulness_declarations())
    D.update(anti_declarations())
    return D


def build(morphs, word: int = 0) -> Struct:
    nodes, real, dom, acc, assoc = [], {}, {}, [], set()
    i = 0
    syl = 0
    for m_index, m in enumerate(morphs):
        flags = {f: (1 if f in m.get("flags", ()) else 0) for f in FLAGS}
        host = None
        pending = []
        for j, v in enumerate(m["segs"]):
            n = NodeId("Or", "lex", i)
            nodes.append(n); real[n] = v
            is_nuc = unstressed(v) in VOWELS
            if "sylls" in m:
                s = m["sylls"][j]
            else:
                s = syl
                if is_nuc:
                    syl += 1
            dom[n] = {"word": word, "syll": s, "morph": m_index, "rank": m["rank"],
                      "side": m["side"], "pwd": m.get("pwd", 0), **flags}
            if j == m.get("acc"):
                host = n
            i += 1
        if m.get("acc") is not None:
            a = NodeId("Acc", "lex", len(acc))
            acc.append(a); real[a] = "A"
            dom[a] = {"word": word, "morph": m_index, "rank": m["rank"],
                      "side": m["side"], "pwd": m.get("pwd", 0), **flags}
            assoc.add((a, host))
    s = Struct(order={"seg": tuple(nodes), "acc": tuple(acc)}, real=real,
               dom=dom, assoc=frozenset(assoc))
    return project(s)


def nuclei(s: Struct):
    return [n for n in s.order["seg"]
            if s.real[n] != ABSENT and unstressed(s.real[n]) in VOWELS]


def project(s: Struct) -> Struct:
    hosts = {b for (a, b) in s.assoc if s.real.get(a) == "A"}
    real = dict(s.real)
    for n in s.order["seg"]:
        v = real[n]
        if v == ABSENT or unstressed(v) not in VOWELS:
            continue
        real[n] = stressed(unstressed(v)) if n in hosts else unstressed(v)
    return Struct(order=s.order, real=real, dom=s.dom, assoc=s.assoc, corr=s.corr)


def well_formed(s: Struct) -> bool:
    hosts = [b for (a, b) in s.assoc if s.real.get(a) == "A"]
    if len(hosts) != len(set(hosts)):
        return False
    linked = {a for (a, b) in s.assoc if s.real.get(a) == "A"}
    for a in s.order.get("acc", ()):
        if s.real.get(a) == "A" and a not in linked:
            return False
    for n in s.order["seg"]:
        v = s.real[n]
        if v == ABSENT or unstressed(v) not in VOWELS:
            continue
        if (v != unstressed(v)) != (n in hosts):
            return False
    return True


def relink(s: Struct, acc: NodeId, host: NodeId | None) -> Struct:
    assoc = frozenset(p for p in s.assoc if p[0] != acc)
    real = dict(s.real)
    if host is not None:
        assoc = assoc | {(acc, host)}
        real[acc] = "A"
    else:
        real[acc] = ABSENT
    return project(Struct(order=s.order, real=real, dom=s.dom, assoc=assoc, corr=s.corr))


def with_made(s: Struct, host: NodeId, index: int = 100) -> Struct:
    a = NodeId("Acc", "made", index)
    order = dict(s.order); order["acc"] = tuple(s.order.get("acc", ())) + (a,)
    real = dict(s.real); real[a] = "A"
    dom = dict(s.dom); dom[a] = dict(s.dom[host]); dom[a].pop("syll", None)
    return project(Struct(order=order, real=real, dom=dom,
                          assoc=frozenset(s.assoc) | {(a, host)}, corr=s.corr))


def surface(s: Struct) -> str:
    import unicodedata
    out, prev = [], None
    for n in s.order["seg"]:
        v = s.real[n]
        if v == ABSENT:
            continue
        if prev is not None and s.dom[n]["morph"] != s.dom[prev]["morph"]:
            out.append("-")
        out.append(v)
        prev = n
    return unicodedata.normalize("NFC", "".join(out))
