from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, Made, NodeId, Not, Or_, Present,
                   RelDecl, Resolves, SameFeat, Scope, Sigma, Slot, SortDecl,
                   Struct, TRUE)

TONES = ("H", "L", "M")


def features():
    f = {
        "H": dict(present=True, hi=True, lo=False, mid=False, sg="undefined", tone=True),
        "L": dict(present=True, hi=False, lo=True, mid=False, sg="undefined", tone=True),
        "M": dict(present=True, hi=False, lo=False, mid=True, sg="undefined", tone=True),
        "σb": dict(present=True, hi="undefined", lo="undefined", mid="undefined", sg=True, tone=False),
        "σm": dict(present=True, hi="undefined", lo="undefined", mid="undefined", sg=False, tone=False),
        ABSENT: dict(present=False, hi=None, lo=None, mid=None, sg=None, tone=None),
    }
    return f


def sigma() -> Sigma:
    sorts = {"Syl": SortDecl("Syl", "total", tier="syll"),
             "Tone": SortDecl("Tone", "total", tier="tone",
                              comment="a lexically supplied autosegment; a candidate tone "
                                      "corresponds to zero, one or two of them"),
             "Rel": SortDecl("Rel", "derived", tier="tone")}
    rels = {"assoc": RelDecl("assoc", "association", "Tone", "Syl", "Rel"),
            "tsucc": RelDecl("tsucc", "succession", "Tone", "Tone", "Rel")}
    return Sigma(sorts=sorts, relations=rels, features=features(),
                 default_features=dict(present=True, hi="undefined", lo="undefined",
                                       mid="undefined", sg="undefined", tone=False),
                 domains=("phrase", "syll", "fin", "pos"))


SAME_SYL = Scope(same=("phrase", "syll"), label="same syllable")
NEXT_SYL = Scope(same=("phrase",), delta={"syll": +1}, label="next syllable")
PREV_SYL = Scope(same=("phrase",), delta={"syll": -1}, label="previous syllable")

T = Slot("t", "Tone", "subject", kind="anchor")
S = Slot("t", "Syl", "subject", kind="anchor")
H_ = Slot("h", "Syl", "trigger", kind="assoc", relation="assoc", tier="syll", where="current")
A_ = Slot("a", "Tone", "subject", kind="assoc", relation="assoc", tier="tone", where="current")
P1 = Slot("p1", "Tone", "subject", kind="step", relation="tsucc", direction=-1, scope=SAME_SYL,
          policy="dynamic")
N1 = Slot("n1", "Tone", "subject", kind="step", relation="tsucc", direction=+1, scope=SAME_SYL,
          policy="dynamic")
N2 = Slot("n2", "Tone", "subject", kind="stepof", relation="tsucc", direction=+1, scope=SAME_SYL,
          of="n1", tier="tone")
X1 = Slot("x1", "Tone", "subject", kind="search", direction=+1, scope=NEXT_SYL)
X2 = Slot("x2", "Tone", "subject", kind="stepof", relation="tsucc", direction=+1, scope=SAME_SYL,
          of="x1", tier="tone")
Q1 = Slot("q1", "Tone", "subject", kind="search", direction=-1, scope=PREV_SYL)
Q0 = Slot("q0", "Tone", "subject", kind="stepof", relation="tsucc", direction=-1, scope=SAME_SYL,
          of="q1", tier="tone")


class _PosOrder:
    def __init__(self, a, b): self.a, self.b = a, b
    def slots(self): return frozenset({self.a, self.b})
    def eval(self, ctx):
        x, y = ctx.resolve(self.a), ctx.resolve(self.b)
        if x is None or y is None: return None
        px = (ctx.state.dom.get(x) or ctx.reference.dom.get(x, {})).get("pos")
        py = (ctx.state.dom.get(y) or ctx.reference.dom.get(y, {})).get("pos")
        if px is None or py is None: return None
        return px < py
    def depth(self): return 1


class _CoordIs:
    def __init__(self, slot, coord, value): self.slot, self.coord, self.value = slot, coord, value
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        d = ctx.state.dom.get(o)
        if d is None:
            d = ctx.reference.dom.get(o, {})
        v = d.get(self.coord)
        return None if v is None else v == self.value
    def depth(self): return 1


def hi(s): return Feat("hi", s, True)
def lo(s): return Feat("lo", s, True)
def mid(s): return Feat("mid", s, True)


FINAL = _CoordIs("t", "fin", 1)
PREV_STARTS_H = Or_((And((Resolves("q0"), hi("q0"))),
                     And((Not(Resolves("q0")), Resolves("q1"), hi("q1")))))
PREV_BARE_L = And((Resolves("q1"), lo("q1"), Not(Resolves("q0"))))
PREV_RISE_OR_MID = Or_((And((Resolves("q1"), mid("q1"))),
                        And((Resolves("q0"), lo("q0"), hi("q1")))))
PREV_LOW_OR_MID = Or_((PREV_BARE_L, And((Resolves("q1"), mid("q1")))))
PREV_FALLS = And((Resolves("q1"), lo("q1"), Resolves("q0"), hi("q0")))
NEXT_BARE_L = And((Resolves("x1"), lo("x1"), Not(Resolves("x2"))))
NEXT_FALLS = And((Resolves("x1"), hi("x1"), Resolves("x2"), lo("x2")))
NEXT_RISES = And((Resolves("x1"), lo("x1"), Resolves("x2"), hi("x2")))
NEXT_STARTS_H = And((Resolves("x1"), hi("x1")))
RISING_HERE = And((lo("t"), Resolves("n1"), hi("n1")))


def declarations(rise_after_fall: bool = True):
    D = {}
    D["TONED"] = Decl("TONED", "Syl", (S, A_), TRUE, Resolves("a"))
    D["FALL_MODAL"] = Decl("FALL_MODAL", "Tone", (T, H_, P1, N1),
                           And((hi("t"), Resolves("h"), Feat("sg", "h", False), Not(Resolves("p1")))),
                           Or_((Not(hi("t")), Resolves("p1"), And((Resolves("n1"), lo("n1"))))))
    D["NOFALL_BREATHY"] = Decl("NOFALL_BREATHY", "Tone", (T, H_, N1),
                               And((hi("t"), Resolves("h"), Feat("sg", "h", True))),
                               Or_((Not(hi("t")), Not(And((Resolves("n1"), lo("n1")))))))
    D["CROWD"] = Decl("CROWD", "Tone", (T, N1, N2), TRUE, Not(And((Resolves("n1"), Resolves("n2")))))
    D["NORISE_FINAL"] = Decl("NORISE_FINAL", "Tone", (T, N1), And((lo("t"), FINAL)),
                             Or_((Not(lo("t")), Not(And((Resolves("n1"), hi("n1")))))))
    D["NO_M_BEFORE_FALL"] = Decl("NO_M_BEFORE_FALL", "Tone", (T, X1, X2), mid("t"), Or_((Not(mid("t")), Not(NEXT_FALLS))))
    D["NO_RISE_RISE"] = Decl("NO_RISE_RISE", "Tone", (T, N1, X1, X2), RISING_HERE, Or_((Not(RISING_HERE), Not(NEXT_RISES))))
    prev_low = Or_((PREV_LOW_OR_MID, PREV_FALLS)) if rise_after_fall else PREV_LOW_OR_MID
    D["NO_RISE_AFTER_LOW"] = Decl("NO_RISE_AFTER_LOW", "Tone", (T, N1, Q1, Q0), RISING_HERE, Or_((Not(RISING_HERE), Not(prev_low))))
    D["NO_RISE_BEFORE_LOW"] = Decl("NO_RISE_BEFORE_LOW", "Tone", (T, N1, X1, X2), RISING_HERE, Or_((Not(RISING_HERE), Not(NEXT_BARE_L))))
    D["NO_M_AFTER_HIGH"] = Decl("NO_M_AFTER_HIGH", "Tone", (T, Q1, Q0), mid("t"), Or_((Not(mid("t")), Not(PREV_STARTS_H))))
    RISING_FALL_HERE = And((hi("t"), Resolves("n1"), lo("n1"), Not(_CoordIs("t", "pos", 0))))
    D["NO_FALL_AFTER_HIGH"] = Decl("NO_FALL_AFTER_HIGH", "Tone", (T, N1, Q1, Q0), RISING_FALL_HERE,
                                   Or_((Not(RISING_FALL_HERE), Not(PREV_STARTS_H))))
    BARE_L_HERE = And((lo("t"), Not(Resolves("n1"))))
    D["NO_L_AFTER_RISE_FINAL"] = Decl("NO_L_AFTER_RISE_FINAL", "Tone", (T, N1, Q1, Q0),
                                      And((BARE_L_HERE, FINAL)), Or_((Not(BARE_L_HERE), Not(PREV_RISE_OR_MID))))
    D["OCP_SYL"] = Decl("OCP_SYL", "Tone", (T, N1), TRUE,
                        Not(And((Resolves("n1"), SameFeat("hi", ("t", "current"), ("n1", "current")),
                                 SameFeat("lo", ("t", "current"), ("n1", "current"))))))
    D["STAR_M"] = Decl("STAR_M", "Tone", (T,), TRUE, Not(mid("t")))
    D["NO_M_CONTOUR"] = Decl("NO_M_CONTOUR", "Tone", (T, P1, N1), mid("t"),
                             Or_((Not(mid("t")), And((Not(Resolves("p1")), Not(Resolves("n1")))))))
    D["FINAL_LOW"] = Decl("FINAL_LOW", "Tone", (T, N1), And((FINAL, Not(Resolves("n1")))), lo("t"))
    D["NO_CONTOUR"] = Decl("NO_CONTOUR", "Tone", (T, N1), TRUE, Not(Resolves("n1")))
    D["MAX_T"] = Decl("MAX_T", "Tone", (T,), TRUE, Present("t"), kind="faithfulness", locus_side="reference")
    D["MAX_FIRST_T"] = Decl("MAX_FIRST_T", "Tone", (T,), _CoordIs("t", "pos", 0), Present("t"),
                            kind="faithfulness", locus_side="reference")
    D["LINEARITY_T"] = Decl("LINEARITY_T", "Tone", (T, N1), And((Resolves("n1"), Not(Made("t")), Not(Made("n1")))),
                            _PosOrder("t", "n1"), kind="faithfulness")
    D["DEP_T"] = Decl("DEP_T", "Tone", (T,), Made("t"), Or_((Not(Made("t")), Not(Present("t")))),
                      kind="faithfulness")
    D["IDENT_T"] = Decl("IDENT_T", "Tone", (T,), TRUE,
                        And((SameFeat("hi", ("t", "current"), ("t", "reference")),
                             SameFeat("lo", ("t", "current"), ("t", "reference")))),
                        kind="faithfulness", locus_side="reference")
    return D


def build(sylls, phrase=0) -> Struct:
    syl_nodes, tone_nodes, real, dom, assoc = [], [], {}, {}, set()
    cont = sylls and sylls[-1] == "+"
    if cont:
        sylls = sylls[:-1]
    k = 0
    for i, (ph, mel) in enumerate(sylls):
        s = NodeId("Syl", "lex", i)
        syl_nodes.append(s); real[s] = "σb" if ph == "b" else "σm"
        fin = 1 if (i == len(sylls) - 1 and not cont) else 0
        dom[s] = {"phrase": phrase, "syll": i, "fin": fin}
        for q, t in enumerate(mel):
            n = NodeId("Tone", "lex", k); k += 1
            tone_nodes.append(n); real[n] = t
            dom[n] = {"phrase": phrase, "syll": i, "fin": fin, "pos": q}
            assoc.add((n, s))
    corr = {s: (s,) for s in syl_nodes}
    corr.update({n: (n,) for n in tone_nodes})
    return Struct(order={"syll": tuple(syl_nodes), "tone": tuple(tone_nodes)}, real=real, dom=dom,
                  assoc=frozenset(assoc), corr=corr)


def syllable_realisations(mel):
    import itertools
    n = len(mel)
    base = []
    for keep in itertools.product([False, True], repeat=n):
        kept = [i for i, kp in enumerate(keep) if kp]
        for levels in itertools.product(*[("H", "L") for _ in kept]):
            seq = tuple(zip(kept, levels))
            base.append(("plain", seq))
            if len(seq) == 2:
                base.append(("plain", (seq[1], seq[0])))
        if len(kept) == 2:
            base.append(("fuse", tuple((i, "M") for i in kept)))
    out = []
    for kind, seq in base:
        for ins in (None, "L", "H"):
            out.append((kind, seq, ins))
    return out


def realise_syllable(ref, s, tones, choice, j):
    kind, seq, ins = choice
    d = dict(ref.dom[s]); d.pop("pos", None)
    nodes, real, dom, assoc, corr = [], {}, {}, set(), {}
    if kind == "fuse":
        n = NodeId("Tone", "out", j); j += 1
        nodes.append(n); real[n] = "M"; dom[n] = dict(d); assoc.add((n, s)); corr[n] = tuple(tones[i] for i, _ in seq)
    else:
        for i, lev in seq:
            n = NodeId("Tone", "out", j); j += 1
            nodes.append(n); real[n] = lev; dom[n] = dict(d, pos=i); assoc.add((n, s)); corr[n] = (tones[i],)
    if ins:
        n = NodeId("Tone", "made", j); j += 1
        nodes.append(n); real[n] = ins; dom[n] = dict(d); assoc.add((n, s)); corr[n] = ()
    return nodes, real, dom, assoc, corr, j


def assemble(ref, choices):
    syls = list(ref.order["syll"])
    by_syl = {s: [n for n in ref.order["tone"] if (n, s) in ref.assoc] for s in syls}
    nodes, real, dom, assoc, corr = [], {}, {}, set(), {}
    j = 0
    for s, ch in zip(syls, choices):
        ns, r, dm, a, c, j = realise_syllable(ref, s, by_syl[s], ch, j)
        nodes += ns; real.update(r); dom.update(dm); assoc |= a; corr.update(c)
    corr.update({s: (s,) for s in syls})
    return Struct(order={"syll": tuple(syls), "tone": tuple(nodes)},
                  real={**{s: ref.real[s] for s in syls}, **real},
                  dom={**{s: ref.dom[s] for s in syls}, **dom},
                  assoc=frozenset(assoc), corr=corr)


def candidates(ref: Struct):
    import itertools
    syls = list(ref.order["syll"])
    by_syl = {s: [n for n in ref.order["tone"] if (n, s) in ref.assoc] for s in syls}
    per = [syllable_realisations("".join(ref.real[n] for n in by_syl[s])) for s in syls]
    for combo in itertools.product(*per):
        yield assemble(ref, combo)


def surface(s: Struct) -> str:
    out = []
    for syl in s.order["syll"]:
        mel = "".join(s.real[n] for n in s.order["tone"] if (n, syl) in s.assoc)
        out.append(mel or "0")
    return "-".join(out)


def build_m(sylls, phrase=0) -> Struct:
    conv = [((ph, "M") if mel == "LH" else (ph, mel)) if isinstance(x, tuple) else x
            for x in sylls for ph, mel in ([x] if isinstance(x, tuple) else [("", "")])]
    return build(conv, phrase)


def candidates_m(ref: Struct):
    import itertools
    syls = list(ref.order["syll"])
    by_syl = {s: [n for n in ref.order["tone"] if (n, s) in ref.assoc] for s in syls}
    per = []
    for s in syls:
        opts = []
        tones = by_syl[s]
        choices = []
        for n in tones:
            c = [("absent", n, None), ("keep", n, "H"), ("keep", n, "L"), ("keep", n, "M")]
            if ref.real[n] == "M":
                c.append((("fission", "LH"), n, None))
                c.append((("fission", "HL"), n, None))
            choices.append(c)
        for combo in itertools.product(*choices):
            for ins in (None, "L", "H"):
                opts.append((combo, ins))
        per.append(opts)
    for combo in itertools.product(*per):
        nodes, real, dom, assoc, corr = [], {}, {}, set(), {}
        j = 0
        for s, (tone_choices, ins) in zip(syls, combo):
            d = dict(ref.dom[s])
            for kind, n, val in tone_choices:
                if kind == "absent":
                    continue
                if kind == "keep":
                    m = NodeId("Tone", "out", j); j += 1
                    nodes.append(m); real[m] = val; dom[m] = dict(d); assoc.add((m, s)); corr[m] = (n,)
                else:
                    for val2 in kind[1]:
                        m = NodeId("Tone", "out", j); j += 1
                        nodes.append(m); real[m] = val2; dom[m] = dict(d); assoc.add((m, s)); corr[m] = (n,)
            if ins:
                m = NodeId("Tone", "made", j); j += 1
                nodes.append(m); real[m] = ins; dom[m] = dict(d); assoc.add((m, s)); corr[m] = ()
        corr.update({s: (s,) for s in syls})
        yield Struct(order={"syll": tuple(syls), "tone": tuple(nodes)},
                     real={**{s: ref.real[s] for s in syls}, **real},
                     dom={**{s: ref.dom[s] for s in syls}, **dom},
                     assoc=frozenset(assoc), corr=corr)
