from __future__ import annotations

import itertools
import unicodedata

from .core import (ABSENT, And, Decl, Feat, Made, NodeId, Not, Or_, Present,
                   RelDecl, Resolves, SameFeat, Scope, Sigma, Slot, SortDecl,
                   Struct, TRUE, UNDEF)

GL = "’"
ACUTE = "́"
DACUTE = "̋"
CONS = {}
for c in ("p", "t", "k", "q", "c"):
    CONS[c] = (0, False, False); CONS[c + GL] = (0, True, False)
CONS[GL] = (0, True, False)
for c in ("s", "x", "ẋ", "h", "ł"):
    CONS[c] = (1, False, False)
for c in ("m", "n"):
    CONS[c] = (2, False, True); CONS[c + GL] = (2, True, True)
CONS["l"] = (3, False, False); CONS["l" + GL] = (3, True, False)
for c in ("w", "y"):
    CONS[c] = (4, False, False); CONS[c + GL] = (4, True, False)
FLOAT = "N"
SHORT = ("a", "e", "i", "o", "u")
LONG = tuple(v + v for v in SHORT)
VOWELS = SHORT + LONG
FRONT = ("i", "ii", "e", "ee")
FLAGS = ("alt", "app2")
FUSION = {("n" + GL, "i"): "y" + GL, ("n" + GL, "y"): "y" + GL, (FLOAT, "s"): "c", ("n", "s"): "c"}


def stressed(v: str) -> str:
    return v[0] + ACUTE + v[1:]


def unstressed(v: str) -> str:
    return v.replace(ACUTE, "")


def features():
    f = {}
    for v in VOWELS:
        row = dict(present=True, nuclear=True, cons=False, long=v in LONG, front=v in FRONT,
                   son=5, glot=False, nasal=False, sonc=False, floating=False)
        f[v] = dict(row, stress=False)
        f[stressed(v)] = dict(row, stress=True)
    for c, (son, glot, nas) in CONS.items():
        f[c] = dict(present=True, nuclear=False, cons=True, long=False, front=None, son=son,
                    glot=glot, nasal=nas, sonc=son >= 2, floating=False, stress=False)
    f[FLOAT] = dict(present=True, nuclear=False, cons=True, long=False, front=None, son=2,
                    glot=False, nasal=True, sonc=True, floating=True, stress=False)
    f[ABSENT] = dict(present=False, nuclear=None, cons=None, long=None, front=None, son=None,
                     glot=None, nasal=None, sonc=None, floating=None, stress=None)
    return f


def sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=features(),
                 default_features=dict(present=True, nuclear=False, cons=True, long=False,
                                       front=False, son=0, glot=False, nasal=False, sonc=False,
                                       floating=False, stress=False),
                 domains=("word", "morph", "level", "cycle", "side", "acc", "accd") + FLAGS)


SG = sigma()

WORD = Scope(same=("word",), label="word")
T = Slot("t", "Or", "subject", kind="anchor")
N1 = Slot("n1", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=+1,
          filter="present", policy="dynamic")
N2 = Slot("n2", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=+1,
          filter="present", of="n1", tier="seg")
N3 = Slot("n3", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=+1,
          filter="present", of="n2", tier="seg")
P1 = Slot("p1", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=-1,
          filter="present", policy="dynamic")
PV = Slot("pv", "Or", "subject", kind="search", direction=-1, scope=WORD, filter="nuclear")
NV = Slot("nv", "Or", "subject", kind="search", direction=+1, scope=WORD, filter="nuclear")
SR = Slot("sr", "Or", "subject", kind="search", direction=+1, scope=WORD, filter="stressed")
NV2 = Slot("nv2", "Or", "subject", kind="search", direction=+1, scope=WORD, filter="nuclear",
           of="nv", tier="seg")
NVN1 = Slot("nvn1", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=+1,
            filter="present", of="nv", tier="seg")
NVN2 = Slot("nvn2", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=+1,
            filter="present", of="nvn1", tier="seg")
SLA = Slot("sla", "Or", "subject", kind="search", direction=-1, scope=WORD, filter="stressed",
           coord=(("accd", 1),))
SRA = Slot("sra", "Or", "subject", kind="search", direction=+1, scope=WORD, filter="stressed",
           coord=(("accd", 1),))
DR = Slot("dr", "Or", "subject", kind="search", direction=+1, scope=WORD, filter="nuclear",
          coord=(("acc", 2),))


class _CoordIs:
    def __init__(self, slot, coord, value): self.slot, self.coord, self.value = slot, coord, value
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        d = ctx.state.dom.get(o, ctx.reference.dom.get(o, {}))
        v = d.get(self.coord)
        if v is None: return None
        return v in self.value if isinstance(self.value, tuple) else v == self.value
    def depth(self): return 1


class _RefNext:
    def __init__(self, slot, coord, value): self.slot, self.coord, self.value = slot, coord, value
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        ref = ctx.reference
        if o not in ref.real:
            cs = ctx.state.correspondents(o)
            if len(cs) != 1: return None
            o = cs[0]
        order = list(ref.order["seg"])
        i = order.index(o)
        for n in order[i + 1:]:
            r = ref.real[n]
            if not ctx.sigma.present(r):
                continue
            if ctx.sigma.ft(r, "nuclear") is not True:
                return False
            return ref.dom[n].get(self.coord) == self.value
        return False
    def depth(self): return 1


class _RefAnyMorphV:
    def __init__(self, slot): self.slot = slot
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        ref = ctx.reference
        if o not in ref.real:
            cs = ctx.state.correspondents(o)
            if len(cs) != 1: return None
            o = cs[0]
        order = list(ref.order["seg"])
        i = order.index(o)
        m0 = ref.dom[o]["morph"]
        for k in range(i + 1, len(order)):
            n = order[k]; d = ref.dom[n]
            if d["morph"] == m0 or d["level"] != 0:
                continue
            if ref.dom[order[k - 1]]["morph"] != d["morph"]:
                if ctx.sigma.ft(ref.real[n], "nuclear") is True:
                    return True
        return False
    def depth(self): return 1


class _SonDrop:
    def __init__(self, a, b): self.a, self.b = a, b
    def slots(self): return frozenset({self.a, self.b})
    def eval(self, ctx):
        x, y = ctx.resolve(self.a), ctx.resolve(self.b)
        if x is None or y is None: return None
        rx, ry = ctx.realisation(x, "current"), ctx.realisation(y, "current")
        if rx is None or ry is None: return None
        sx, sy = ctx.sigma.ft(rx, "son"), ctx.sigma.ft(ry, "son")
        if sx is UNDEF or sy is UNDEF or sx is None or sy is None or sx == "undefined" or sy == "undefined": return None
        return sx >= sy
    def depth(self): return 1


class _Fused:
    def __init__(self, slot): self.slot = slot
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        st = ctx.state
        if st.corr is None:
            return False
        if o in st.real:
            return len(st.correspondents(o)) > 1
        im = ctx._inv.get(o, ())
        if len(im) != 1:
            return None
        return len(st.correspondents(im[0])) > 1
    def depth(self): return 1


class _LostSlots:
    def __init__(self, slot, k): self.slot, self.k = slot, k
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        st = ctx.state
        if st.corr is None or o not in st.real:
            return False
        cs = st.correspondents(o)
        if len(cs) < 2:
            return False
        span = sum(2 if ctx.reference.real[c] in LONG else 1 for c in cs)
        out = 2 if st.real[o] in LONG or unstressed(st.real[o]) in LONG else 1
        return span - out >= self.k
    def depth(self): return 1


def nuc(s, where="current"): return Feat("nuclear", s, True, where=where)
def cons(s): return Feat("cons", s, True)
def long_(s, where="current"): return Feat("long", s, True, where=where)
def st(s): return Feat("stress", s, True)
def lvl0(s): return _CoordIs(s, "level", 0)


ENV_OPEN = And((Not(long_("t")), Not(st("t")), Resolves("pv"), Resolves("n1"), cons("n1"),
                Resolves("n2"), nuc("n2"), lvl0("n2")))
ENV_OPEN_ANY = And((Not(long_("t")), Not(st("t")), Resolves("pv"), Resolves("n1"), cons("n1"),
                    Resolves("n2"), nuc("n2")))
ENV_ALL = And((Not(long_("t")), Not(st("t")), Resolves("pv"), Resolves("nv"), lvl0("nv")))
ENV_ALL_ANY = And((Not(long_("t")), Not(st("t")), Resolves("pv"), Resolves("nv")))


def syncope(name, env, level_anchor=True):
    act = [nuc("t"), _CoordIs("t", "acc", 0), env]
    if level_anchor:
        act.insert(1, lvl0("t"))
    return Decl(name, "Or", (T, PV, NV, N1, N2), And(tuple(act)),
                Or_((Not(Present("t")), Not(nuc("t")), Not(env))), scope=WORD)


def declarations(level_scoped: bool = True, shorten: bool = True, ref_weight: bool = False,
                 env: str = "all"):
    D = {}
    if env == "open":
        e = ENV_OPEN if level_scoped else ENV_OPEN_ANY
    else:
        e = ENV_ALL if level_scoped else ENV_ALL_ANY
    D["SYNCOPE"] = syncope("SYNCOPE", e, level_anchor=level_scoped)
    if shorten:
        D["SHORTEN"] = Decl("SHORTEN", "Or", (T,), And((nuc("t"), long_("t"))),
                            Or_((Not(Present("t")), Not(long_("t")), st("t"))), scope=WORD)
    D["ONSET"] = Decl("ONSET", "Or", (T, P1), nuc("t"),
                      Or_((Not(nuc("t")), And((Resolves("p1"), cons("p1"))))), scope=WORD)
    D["NOCC_INIT"] = Decl("NOCC_INIT", "Or", (T, P1, N1), And((cons("t"), Not(Resolves("p1")))),
                          Or_((Not(cons("t")), Resolves("p1"), Not(Resolves("n1")), nuc("n1"))),
                          scope=WORD)
    coda2 = And((cons("t"), Resolves("n1"), cons("n1"), Resolves("n2"), cons("n2")))
    codas = And((cons("t"), Resolves("n1"), cons("n1"), Or_((Not(Resolves("n2")), cons("n2")))))
    D["CODA_SSP"] = Decl("CODA_SSP", "Or", (T, N1, N2), And((codas, Not(_SonDrop("t", "n1")))),
                         Or_((Not(codas), _SonDrop("t", "n1"))), scope=WORD)
    D["CODA2"] = Decl("CODA2", "Or", (T, N1, N2), coda2, Not(coda2), scope=WORD)
    lw = long_("t", "reference") if ref_weight else long_("t")
    vvcc = And((nuc("t"), lw, Resolves("n1"), cons("n1"), Resolves("n2"), cons("n2"),
                Or_((Not(Resolves("n3")), cons("n3")))))
    D["VVCC"] = Decl("VVCC", "Or", (T, N1, N2, N3), vvcc, Not(vvcc), scope=WORD)
    rr = And((Feat("sonc", "t", True), Resolves("n1"), Feat("sonc", "n1", True), Feat("glot", "n1", True)))
    D["RR_GLOT"] = Decl("RR_GLOT", "Or", (T, N1), rr, Not(rr), scope=WORD)
    superheavy = And((long_("t", "reference"), Resolves("n1"), cons("n1"), Not(Resolves("n2"))))
    D["RIGHTMOST_DOM"] = Decl("RIGHTMOST_DOM", "Or", (T, DR), And((nuc("t"), _CoordIs("t", "acc", 2))),
                              Or_((Not(nuc("t")), st("t"), Resolves("dr"))), scope=WORD)
    D["ACC_STRESS"] = Decl("ACC_STRESS", "Or", (T, SLA, SRA), And((nuc("t"), _CoordIs("t", "accd", 1))),
                           Or_((Not(nuc("t")), st("t"), Resolves("sla"), Resolves("sra"))), scope=WORD)
    D["LEFTMOST_ACC"] = Decl("LEFTMOST_ACC", "Or", (T, SR), And((nuc("t"), _CoordIs("t", "acc", (1, 2)))),
                             Or_((Not(nuc("t")), Not(Resolves("sr")))), scope=WORD)
    D["NONFIN"] = Decl("NONFIN", "Or", (T, NV, N1, N2), And((nuc("t"), st("t"))),
                       Or_((Not(st("t")), Resolves("nv"), superheavy)), scope=WORD)
    sh_nv = And((long_("nv", "reference"), Resolves("nvn1"), cons("nvn1"), Not(Resolves("nvn2"))))
    D["PENULT"] = Decl("PENULT", "Or", (T, NV, NV2, NVN1, NVN2, N1, N2), And((nuc("t"), st("t"))),
                       Or_((Not(st("t")), _CoordIs("t", "accd", 1),
                            And((Resolves("nv"), Not(Resolves("nv2")), Not(sh_nv))), superheavy)), scope=WORD)
    R = dict(kind="faithfulness", locus_side="reference")
    D["MAX_V"] = Decl("MAX_V", "Or", (T,), nuc("t", "reference"), Present("t"), **R)
    D["MAX_VV"] = Decl("MAX_VV", "Or", (T,), And((nuc("t", "reference"), long_("t", "reference"))),
                       Present("t"), **R)
    D["MAX_ACC"] = Decl("MAX_ACC", "Or", (T,), And((nuc("t", "reference"), _CoordIs("t", "acc", (1, 2)))),
                        Present("t"), **R)
    D["MAX_C"] = Decl("MAX_C", "Or", (T,), And((Feat("cons", "t", True, where="reference"),
                                                Not(Feat("floating", "t", True, where="reference")))),
                      Present("t"), **R)
    D["MAX_FLOAT"] = Decl("MAX_FLOAT", "Or", (T,), Feat("floating", "t", True, where="reference"),
                          Present("t"), **R)
    D["DEP_X"] = Decl("DEP_X", "Or", (T,), Feat("floating", "t", True, where="reference"),
                      Or_((Not(Present("t")), _Fused("t"))), **R)
    D["DEP_X_FINAL"] = Decl("DEP_X_FINAL", "Or", (T, N1), Feat("floating", "t", True, where="reference"),
                            Or_((Not(Present("t")), _Fused("t"), Resolves("n1"))), **R)
    D["IDENT_LONG"] = Decl("IDENT_LONG", "Or", (T,), And((nuc("t", "reference"), long_("t", "reference"))),
                           Or_((Not(Present("t")), long_("t"))), **R)
    D["IDENT_LONG_S"] = Decl("IDENT_LONG_S", "Or", (T,), And((nuc("t", "reference"), long_("t", "reference"), st("t"))),
                             Or_((Not(Present("t")), Not(st("t")), long_("t"))), **R)
    D["IDENT_NUC"] = Decl("IDENT_NUC", "Or", (T,), TRUE,
                          Or_((Not(Present("t")), SameFeat("nuclear", ("t", "current"), ("t", "reference")))), **R)
    D["IDENT_NAS"] = Decl("IDENT_NAS", "Or", (T,), Feat("nasal", "t", True, where="reference"),
                          Or_((Not(Present("t")), Feat("nasal", "t", True))), **R)
    D["IDENT_FRONT"] = Decl("IDENT_FRONT", "Or", (T,), nuc("t", "reference"),
                            Or_((Not(Present("t")), SameFeat("front", ("t", "current"), ("t", "reference")))), **R)
    D["DEP_C"] = Decl("DEP_C", "Or", (T,), Made("t"), Or_((Not(Made("t")), Not(Present("t")))),
                      kind="faithfulness")
    D["UNIF"] = Decl("UNIF", "Or", (T,), _Fused("t"), Not(_Fused("t")), kind="faithfulness")
    D["UNIF2"] = Decl("UNIF2", "Or", (T,), _LostSlots("t", 2), Not(_LostSlots("t", 2)), kind="faithfulness")
    D["SEL_SISTER"] = listed_declarations()["SEL_SISTER"]
    return D


def listed_declarations():
    short = Or_((Not(Present("t")), Not(nuc("t"))))
    cvnext = And((Resolves("n1"), cons("n1"), Resolves("n2"), nuc("n2"), lvl0("n2")))
    allo = Decl("ALLO_OUT", "Or", (T, N1, N2), _CoordIs("t", "app2", 1),
                Or_((And((short, cvnext)), And((Not(short), Not(cvnext))))),
                kind="faithfulness", locus_side="reference")
    vsis = _RefNext("t", "cycle", 1)
    sel = Decl("SEL_SISTER", "Or", (T,), _CoordIs("t", "alt", 1),
               Or_((And((Feat("front", "t", True), vsis)), And((Not(Feat("front", "t", True)), Not(vsis))))),
               kind="faithfulness", locus_side="reference")
    vany = _RefAnyMorphV("t")
    sel2 = Decl("SEL_ANY", "Or", (T,), _CoordIs("t", "alt", 1),
                Or_((And((Feat("front", "t", True), vany)), And((Not(Feat("front", "t", True)), Not(vany))))),
                kind="faithfulness", locus_side="reference")
    return {d.name: d for d in (allo, sel, sel2)}


def tokenize(m: str):
    s = unicodedata.normalize("NFD", m)
    out, i = [], 0
    while i < len(s):
        ch = s[i]
        if ch in SHORT:
            acc = 0
            j = i + 1
            if j < len(s) and s[j] in (ACUTE, DACUTE):
                acc = 1 if s[j] == ACUTE else 2; j += 1
            if j < len(s) and s[j] == ch:
                j += 1
                if j < len(s) and s[j] in (ACUTE, DACUTE):
                    acc = 1 if s[j] == ACUTE else 2; j += 1
                out.append((ch + ch, acc))
            else:
                out.append((ch, acc))
            i = j
        elif ch == FLOAT:
            out.append((FLOAT, 0)); i += 1
        else:
            j = i + 1
            if j < len(s) and s[j] == GL and ch != GL:
                out.append((ch + GL, 0)); i = j + 1
            else:
                out.append((ch, 0)); i = j
            assert out[-1][0] in CONS, (m, out[-1])
    return out


def build(morphs, word: int = 0) -> Struct:
    root = next(i for i, m in enumerate(morphs) if m[2] == 0)
    suf = [i for i in range(root + 1, len(morphs))]
    pre = [i for i in range(root - 1, -1, -1)]
    cycle = {root: 1}
    c = 1
    for k, i in enumerate(suf):
        cycle[i] = 1 if k == 0 else c + 1
        c = cycle[i]
    for i in pre:
        c += 1; cycle[i] = c
    nodes, real, dom = [], {}, {}
    k = 0
    for i, m in enumerate(morphs):
        flags = m[3] if len(m) > 3 else ()
        toks = tokenize(m[0])
        last_v = max((j for j, (sym, _) in enumerate(toks) if sym in VOWELS), default=None)
        for j, (sym, acc) in enumerate(toks):
            n = NodeId("Or", "lex", k); k += 1
            nodes.append(n); real[n] = sym
            fl = {f: (1 if f in flags else 0) for f in FLAGS}
            if fl.get("app2") and j != last_v:
                fl["app2"] = 0
            dom[n] = {"word": word, "morph": i, "level": m[1], "cycle": cycle[i], "side": m[2],
                      "acc": acc, "accd": int(acc > 0), **fl}
    corr = {n: (n,) for n in nodes}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom, corr=corr)


def candidates(ref: Struct, front_alt: bool = True):
    order = list(ref.order["seg"])
    per = []
    i = 0
    while i < len(order):
        n = order[i]
        sym = ref.real[n]
        opts = []
        nxt = order[i + 1] if i + 1 < len(order) else None
        nsym = ref.real[nxt] if nxt is not None else None
        if sym in VOWELS:
            opts.append(("del", ()))
            reals = [sym] + ([sym[0]] if sym in LONG else [])
            if front_alt and ref.dom[n]["alt"]:
                reals += [("i" if len(r) == 1 else "ii") if r[0] == "u" else
                          ("u" if len(r) == 1 else "uu") for r in list(reals)]
            for r in reals:
                opts.append(("keep", r))
                if nsym in VOWELS:
                    opts.append(("keep+y", r))
            if sym == "i" and nsym in VOWELS:
                opts.append(("glide", "y"))
            if nsym in VOWELS:
                opts.append(("fuse", nsym[0]))
        elif sym == FLOAT:
            opts += [("del", ()), ("keep", "n")]
        elif sym == "y":
            opts += [("keep", sym), ("vocalise", "i")]
        else:
            opts.append(("keep", sym))
        if nsym is not None and (sym, nsym) in FUSION:
            opts.append(("fuse", FUSION[(sym, nsym)]))
        per.append(opts)
        i += 1
    for combo in itertools.product(*per):
        skip = False
        nodes, real, dom, corr = [], {}, {}, {}
        j = 0
        ok = True
        for idx, (n, (kind, val)) in enumerate(zip(order, combo)):
            if skip:
                skip = False
                if kind != "keep" or val != ref.real[n]:
                    ok = False; break
                continue
            if kind == "del":
                continue
            if kind == "fuse":
                m = NodeId("Or", "out", j); j += 1
                nxt = order[idx + 1]
                d = dict(ref.dom[n])
                d["acc"] = max(ref.dom[n]["acc"], ref.dom[nxt]["acc"]); d["accd"] = int(d["acc"] > 0)
                nodes.append(m); real[m] = val; dom[m] = d; corr[m] = (n, nxt)
                skip = True
                continue
            m = NodeId("Or", "out", j); j += 1
            nodes.append(m); real[m] = val if kind != "keep+y" else val; dom[m] = dict(ref.dom[n]); corr[m] = (n,)
            if kind == "keep+y":
                g = NodeId("Or", "made", j); j += 1
                nodes.append(g); real[g] = "y"; dom[g] = dict(ref.dom[n]); corr[g] = ()
        if not ok:
            continue
        nucs = [m for m in nodes if real[m] in VOWELS]
        if not nucs:
            continue
        for h in nucs:
            r2 = dict(real); r2[h] = stressed(real[h])
            yield Struct(order={"seg": tuple(nodes)}, real=r2, dom=dom, corr=corr)


def surface(s: Struct) -> str:
    out = [s.real[n] for n in s.order["seg"] if s.real[n] != ABSENT]
    return unicodedata.normalize("NFC", "".join(out))
