from __future__ import annotations

from fractions import Fraction

from .core import (ABSENT, And, Decl, Feat, InScope, Linked, NodeId, Not, Or_,
                   Present, RelDecl, Resolves, SameFeat, Scope, Sigma, Slot,
                   SortDecl, Struct, TRUE)

SEGS = {"a": {"present": True, "bearer": True, "tone": "undefined"},
        "H": {"present": True, "bearer": False, "tone": "H"},
        ABSENT: {"present": False, "bearer": "undefined", "tone": "undefined"}}


def make_sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Tone": SortDecl("Tone", "total", tier="tone"),
                        "Rel": SortDecl("Rel", "derived", tier="seg"),
                        "ToneRel": SortDecl("ToneRel", "derived", tier="tone"),
                        "Assoc": SortDecl("Assoc", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel"),
                            "tone_succ": RelDecl("tone_succ", "succession", "Tone", "Tone", "ToneRel"),
                            "assoc": RelDecl("assoc", "association", "Tone", "Or", "Assoc")},
                 features=SEGS,
                 default_features={"present": True, "bearer": False,
                                   "tone": "undefined"},
                 domains=("word",))


WORD = Scope(same=("word",), label="word")
T = Slot("t", "Tone", "subject", kind="anchor")
HOST = Slot("h", "Or", "subject", kind="assoc", relation="assoc",
            where="current", tier="seg")
HNEXT = Slot("hn", "Or", "subject", kind="stepof", relation="succ", scope=WORD,
             direction=+1, tier="seg", of="h")
HPREV = Slot("hp", "Or", "subject", kind="stepof", relation="succ", scope=WORD,
             direction=-1, tier="seg", of="h")
TNEXT = Slot("tn", "Tone", "subject", kind="step", relation="tone_succ", scope=WORD,
             direction=+1, tier="tone")
TPREV = Slot("tp", "Tone", "subject", kind="step", relation="tone_succ", scope=WORD,
             direction=-1, tier="tone")


def adjacent_pair(other, left, right):
    return And((Present("t"), Present(other), Linked("t", left), Linked(other, right)))


OCP_CONTEXT = Or_(tuple(adjacent_pair(other, left, right)
                        for other in ("tn", "tp")
                        for left, right in (("h", "hn"), ("hp", "h"))))
OCP_BAD = Or_(tuple(And((adjacent_pair(other, left, right),
                         SameFeat("tone", ("t", "current"), (other, "current"))))
                    for other in ("tn", "tp")
                    for left, right in (("h", "hn"), ("hp", "h"))))

OCP = Decl("OCP", "Tone", (T, HOST, HNEXT, HPREV, TNEXT, TPREV),
           OCP_CONTEXT, Not(OCP_BAD),
           scope=WORD)

PARSE_T = Decl("PARSE-T", "Tone", (T,), TRUE, Present("t"),
               kind="faithfulness", locus_side="reference")
HOSTREF = Slot("h", "Or", "subject", kind="assoc", relation="assoc",
               where="reference", tier="seg")
PARSE_A = Decl("PARSE-A", "Tone", (T, HOSTREF), TRUE,
               Or_((Not(Resolves("h")), Linked("t", "h", where="current"))),
               kind="faithfulness", locus_side="reference")

DECLS = {"PARSE-T": PARSE_T, "PARSE-A": PARSE_A, "OCP": OCP}
LAM = Fraction(1, 8)


def build(tones, links):
    segs = ("a", "a")
    segn = tuple(NodeId("Or", "lex", i) for i in range(len(segs)))
    tonn = tuple(NodeId("Tone", "lex", i) for i in range(len(tones)))
    real = {n: segs[i] for i, n in enumerate(segn)}
    real.update({n: tones[i] for i, n in enumerate(tonn)})
    dom = {n: {"word": 0, "pos": i} for i, n in enumerate(segn)}
    dom.update({n: {"word": 0, "pos": i} for i, n in enumerate(tonn)})
    assoc = frozenset((tonn[i], segn[j]) for i, j in links.items() if j is not None)
    return Struct(order={"seg": segn, "tone": tonn}, real=real, dom=dom, assoc=assoc)


def describe(s):
    ts = [s.real[n] for n in s.nodes("tone")]
    tone_positions = {n: i for i, n in enumerate(s.nodes("tone"))}
    bearer_positions = {n: i for i, n in enumerate(s.nodes("seg"))}
    links = {}
    for a, b in s.assoc:
        if a in bearer_positions and b in tone_positions:
            a, b = b, a
        links.setdefault(tone_positions[a], set()).add(bearer_positions[b])
    def hosts(i):
        values = sorted(links.get(i, ()))
        if not values:
            return "x"
        if len(values) == 1:
            return str(values[0])
        return "{" + ",".join(map(str, values)) + "}"
    return "".join(t if t != ABSENT else "-" for t in ts) + \
           "/" + ",".join(f"{i}->{hosts(i)}" for i in range(len(ts)))
