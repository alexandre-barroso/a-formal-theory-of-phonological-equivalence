from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, InScope, Linked, Made, NodeId, Not,
                   Or_, Positional, Present, RelDecl, Resolves, SameFeat, Scope,
                   Sigma, Slot, SortDecl, Struct, TRUE)

SHORT = ("a", "e", "i", "o", "u")
LONG = ("aa", "ee", "ii", "oo", "uu", "ei", "ou", "oi", "ie")
CONS = ("b", "t", "c", "k", "ʔ", "θ", "s", "x", "h", "n", "y", "w")


def _v(long, high, stress=False):
    return dict(present=True, nuclear=True, long=long, high=high, stress=stress)


def stressed(v: str) -> str:
    return "".join(ch + "\u0301" for ch in v)


def unstressed(v: str) -> str:
    return v.replace("\u0301", "")


def _c():
    return dict(present=True, nuclear=False, long=False, high=False, stress=False)


def features(mode: str):
    f = {}
    for v in SHORT:
        f[v] = _v(False, v in ("i", "u"))
    for v in LONG:
        f[v] = _v(True, v in ("ii", "uu"))
    if mode == "feature":
        for v in SHORT + LONG:
            f[stressed(v)] = dict(f[v], stress=True)
    for c in CONS:
        f[c] = _c()
    f["A"] = dict(present=True, nuclear=False, long=False, high=False, stress=False)
    f[ABSENT] = dict(present=False, nuclear=None, long=None, high=None, stress=None)
    return f


def sigma(mode: str = "node") -> Sigma:
    if mode not in ("node", "feature"):
        raise ValueError(mode)
    sorts = {"Or": SortDecl("Or", "total", tier="seg"),
             "Rel": SortDecl("Rel", "derived", tier="seg")}
    rels = {"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")}
    if mode == "node":
        sorts["Acc"] = SortDecl("Acc", "total", tier="acc",
                                comment="a lexically supplied accent mark")
        rels["assoc"] = RelDecl("assoc", "association", "Acc", "Or", "Rel")
    return Sigma(sorts=sorts, relations=rels, features=features(mode),
                 default_features=dict(present=True, nuclear=False, long=False,
                                       high=False, stress=False),
                 domains=("syll", "word", "morph"))


WORD = Scope(same=("word",), label="word")
PREV_MORPH = Scope(delta={"morph": -1}, label="previous morph")
SAME_MORPH = Scope(same=("morph",), label="same morph")

T = Slot("t", "Or", "subject", kind="anchor")
NX = Slot("n", "Or", "subject", kind="step", relation="succ", scope=WORD,
          direction=+1, filter="nuclear", filter_mode="skip", policy="dynamic")
NXT = Slot("n", "Or", "trigger", kind="step", relation="succ", scope=WORD,
           direction=+1, filter="nuclear", filter_mode="skip", policy="dynamic")
N2 = Slot("n2", "Or", "subject", kind="stepof", of="n", relation="succ",
          scope=WORD, direction=+1, filter="nuclear", filter_mode="skip")
P1 = Slot("p1", "Or", "subject", kind="step", relation="succ", scope=WORD,
          direction=-1, filter="nuclear", filter_mode="skip", policy="dynamic")
P2 = Slot("p2", "Or", "subject", kind="stepof", of="p1", relation="succ",
          scope=WORD, direction=-1, filter="nuclear", filter_mode="skip")
A0 = Slot("a", "Acc", "subject", kind="assoc", relation="assoc", tier="acc")
A0T = Slot("a", "Acc", "trigger", kind="assoc", relation="assoc", tier="acc")
AN = Slot("an", "Acc", "subject", kind="assocof", of="n", relation="assoc",
          tier="acc", scope=WORD)
ANT = Slot("an", "Acc", "trigger", kind="assocof", of="n", relation="assoc",
           tier="acc", scope=WORD)
A1 = Slot("a1", "Acc", "subject", kind="assocof", of="p1", relation="assoc",
          tier="acc", scope=WORD)
A2 = Slot("a2", "Acc", "subject", kind="assocof", of="p2", relation="assoc",
          tier="acc", scope=WORD)
TA = Slot("t", "Acc", "subject", kind="anchor")
H = Slot("h", "Or", "subject", kind="assoc", relation="assoc", tier="seg",
         where="current")
HT = Slot("h", "Or", "trigger", kind="assoc", relation="assoc", tier="seg",
          where="current")
HREF = Slot("hr", "Or", "subject", kind="assoc", relation="assoc", tier="seg",
            where="reference")
HREFT = Slot("hr", "Or", "trigger", kind="assoc", relation="assoc", tier="seg",
             where="reference")

FINAL_NUC = Positional("last_live_of", "t", "word", "nuclear")


def node_declarations(select: str = "R"):
    host_next = Slot("hn", "Or", "subject", kind="stepof", of="h",
                     relation="succ", scope=SAME_MORPH, direction=+1,
                     filter="nuclear", filter_mode="skip", tier="seg")
    osd = Decl("OSD", "Or", (T, P1, P2, A0, A1, A2), FINAL_NUC,
               Or_((Resolves("a"), Resolves("a1"), Resolves("a2"))), scope=WORD)
    nonfinal = Decl("NONFINAL", "Or", (T, A0T), Resolves("a"),
                    Not(FINAL_NUC), scope=WORD)
    rightmost = Decl("RIGHTMOST", "Or", (T, A0T, NXT, N2),
                     And((Resolves("a"), Resolves("n"))),
                     Not(Resolves("n2")), scope=WORD)
    if select == "R":
        clash = Decl("CLASH", "Or", (T, A0, NXT, ANT),
                     And((Resolves("a"), Resolves("n"), Resolves("an"))),
                     Not(Resolves("a")), scope=WORD)
    else:
        clash = Decl("CLASH", "Or", (T, A0T, NX, AN),
                     And((Resolves("a"), Resolves("n"), Resolves("an"))),
                     Not(Resolves("an")), scope=WORD)
    flt = Decl("FLOAT", "Acc", (TA, H), Present("t"), Resolves("h"))
    dock = Decl("DOCK_PREV", "Acc", (TA, H, HREFT, host_next),
                And((Present("t"), Not(Made("t")), Not(Resolves("hr")))),
                And((Resolves("h"), InScope("h", PREV_MORPH, "t"),
                     Not(Resolves("hn")))))
    local = Decl("LOCAL", "Acc", (TA, H, HREFT),
                 And((Present("t"), Resolves("hr"), Resolves("h"))),
                 InScope("h", SAME_MORPH, "t"))
    max_acc = Decl("MAX_ACC", "Acc", (TA,), TRUE, Present("t"),
                   kind="faithfulness", locus_side="reference")
    maxlink = Decl("MAXLINK", "Acc", (TA, HREF), TRUE,
                   Linked("t", "hr", where="current"), kind="faithfulness",
                   locus_side="reference")
    deplink = Decl("DEPLINK", "Acc", (TA, H), TRUE,
                   Or_((Not(Resolves("h")), Linked("t", "h", where="reference"))),
                   kind="faithfulness")
    dep_acc = Decl("DEP_ACC", "Acc", (TA,), Made("t"),
                   Or_((Not(Made("t")), Not(Present("t")))), kind="faithfulness")
    return {d.name: d for d in (osd, nonfinal, rightmost, clash, flt, dock, local,
                                max_acc, maxlink, deplink, dep_acc)}


def feature_declarations(select: str = "R", guarded: bool = True):
    st = lambda s: Feat("stress", s, True)
    if guarded:
        cons = Or_((st("t"), And((Resolves("p1"), st("p1"))),
                    And((Resolves("p2"), st("p2")))))
    else:
        cons = Or_((st("t"), st("p1"), st("p2")))
    osd = Decl("OSD", "Or", (T, P1, P2), FINAL_NUC, cons, scope=WORD)
    nonfinal = Decl("NONFINAL", "Or", (T,), st("t"), Not(FINAL_NUC), scope=WORD)
    rightmost = Decl("RIGHTMOST", "Or", (T, NXT, N2),
                     And((st("t"), Resolves("n"))), Not(Resolves("n2")), scope=WORD)
    if select == "R":
        clash = Decl("CLASH", "Or", (T, NXT),
                     And((st("t"), Resolves("n"), st("n"))),
                     Feat("stress", "t", False), scope=WORD)
    else:
        clash = Decl("CLASH", "Or", (T, NX),
                     And((st("t"), Resolves("n"), st("n"))),
                     Feat("stress", "n", False), scope=WORD)
    ident = Decl("ID_STRESS", "Or", (T,), Not(Made("t")),
                 SameFeat("stress", ("t", "current"), ("t", "reference")),
                 kind="faithfulness", locus_side="reference")
    return {d.name: d for d in (osd, nonfinal, rightmost, clash, ident)}


def build(segs, sylls, morphs, accents=(), made_nuclei=(), made_dom=None):
    nodes, real, dom = [], {}, {}
    for i, v in enumerate(segs):
        n = NodeId("Or", "made" if i in made_nuclei else "lex", i)
        nodes.append(n); real[n] = v
        dom[n] = {"syll": sylls[i], "word": 0, "morph": morphs[i]}
    acc, assoc = [], set()
    for k, (m, host) in enumerate(accents):
        a = NodeId("Acc", "lex", k)
        acc.append(a); real[a] = "A"; dom[a] = {"word": 0, "morph": m}
        if host is not None:
            assoc.add((a, nodes[host]))
    return Struct(order={"seg": tuple(nodes), "acc": tuple(acc)}, real=real,
                  dom=dom, assoc=frozenset(assoc))


def relink(s: Struct, acc: NodeId, host: NodeId | None, present: bool = True):
    assoc = frozenset(p for p in s.assoc if p[0] != acc)
    if host is not None and present:
        assoc = assoc | {(acc, host)}
    real = dict(s.real); real[acc] = "A" if present else ABSENT
    return Struct(order=s.order, real=real, dom=s.dom, assoc=assoc, corr=s.corr)


def with_default(s: Struct, host: NodeId | None, morph: int):
    a = NodeId("Acc", "made", 100)
    order = dict(s.order); order["acc"] = tuple(s.order.get("acc", ())) + (a,)
    real = dict(s.real); real[a] = "A" if host is not None else ABSENT
    dom = dict(s.dom); dom[a] = {"word": 0, "morph": morph}
    assoc = set(s.assoc)
    if host is not None:
        assoc.add((a, host))
    return Struct(order=order, real=real, dom=dom, assoc=frozenset(assoc), corr=s.corr)


def insert_after(s: Struct, index: int, value: str, syll: int, morph: int,
                 made_index: int = 100) -> Struct:
    order = list(s.order["seg"])
    host = order[index]
    made = NodeId("Or", "made", made_index)
    order.insert(index + 1, made)
    real = dict(s.real); real[made] = value
    dom = dict(s.dom); dom[made] = {"syll": syll, "word": 0, "morph": morph}
    return Struct(order={**s.order, "seg": tuple(order)}, real=real, dom=dom,
                  assoc=s.assoc, corr=s.corr)


def nuclei(s: Struct, sg: Sigma | None = None):
    sg = sg or sigma("node")
    return [n for n in s.order["seg"]
            if sg.present(s.real[n]) and sg.ft(s.real[n], "nuclear") is True]


def surface(s: Struct) -> str:
    out, prev = [], None
    hosts = {b for (a, b) in s.assoc if s.real.get(a) == "A"}
    for n in s.order["seg"]:
        v = s.real[n]
        if v == ABSENT:
            continue
        if prev is not None and s.dom[n]["syll"] != s.dom[prev]["syll"]:
            out.append(".")
        out.append(stressed(v) if n in hosts else v)
        prev = n
    return __import__("unicodedata").normalize("NFC", "".join(out))
