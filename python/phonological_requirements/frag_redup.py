from __future__ import annotations

import itertools

from .core import (ABSENT, And, Decl, Feat, NodeId, Not, Or_, RelDecl, Resolves, SameFeat,
                   Scope, Sigma, Slot, SortDecl, Struct, TRUE, Term, Present)

WORD = Scope(same=("word",), label="word")
VOWELS = "aeiou"
CONS = "ptkcsxhmnlwyq?"
FLAGS = ("red", "L", "base")


def vsym(v, long_, stress, parsed):
    if stress is None:
        mark = ""
    else:
        mark = "'" if stress else ("." if parsed else "_")
    return mark + v + ("ː" if long_ else "")


def make_sigma() -> Sigma:
    f = {}
    for c in CONS:
        for g in (False, True):
            f[c + ("'" if g else "")] = dict(present=True, nuclear=False, glott=g, long=None, stressed=None, parsed=None)
    for v in VOWELS:
        for long_ in (False, True):
            f[vsym(v, long_, None, None)] = dict(present=True, nuclear=True, glott=None, long=long_,
                                                stressed=None, parsed=None, quality=v)
            for stress in (False, True):
                for parsed in ((True,) if stress else (True, False)):
                    f[vsym(v, long_, stress, parsed)] = dict(present=True, nuclear=True, glott=None, long=long_,
                                                           stressed=stress, parsed=parsed, quality=v)
    f[ABSENT] = dict(present=False, nuclear=None, glott=None, long=None, stressed=None, parsed=None, quality=None)
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"), "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=f, default_features={"present": True, "nuclear": False}, domains=("word",))


def tokenize(m: str):
    out, i = [], 0
    while i < len(m):
        ch = m[i]
        if ch in VOWELS:
            if i + 1 < len(m) and m[i + 1] == ch:
                out.append(vsym(ch, True, None, None)); i += 2
            else:
                out.append(vsym(ch, False, None, None)); i += 1
        else:
            if i + 1 < len(m) and m[i + 1] == "'":
                out.append(ch + "'"); i += 2
            else:
                out.append(ch); i += 1
    return out


def is_v(sym): return sym is not ABSENT and sym.lstrip("'_.")[0] in VOWELS
def is_long(sym): return is_v(sym) and sym.endswith("ː")
def quality(sym): return sym.lstrip("'_.")[0]
def shorten(sym): return sym[:-1] if is_long(sym) else sym
def restress(sym, stress, parsed):
    return vsym(quality(sym), is_long(sym), stress, parsed)


def info(morphs):
    stem = next(i for i, m in enumerate(morphs) if m[1] == "stem")
    cycle = {stem: 1}
    c = 1
    for k, i in enumerate(range(stem + 1, len(morphs))):
        cycle[i] = 1 if k == 0 else c + 1
        c = cycle[i]
    for i in range(stem - 1, -1, -1):
        c += 1; cycle[i] = c
    return cycle, next((i for i, m in enumerate(morphs) if m[1] == "red"), None)


def build(morphs, word: int = 0) -> Struct:
    cycle, red = info(morphs)
    nodes, real, dom = [], {}, {}
    k = 0
    for i, m in enumerate(morphs):
        flags = m[2] if len(m) > 2 else ()
        if m[1] == "red":
            continue
        for sym in tokenize(m[0]):
            n = NodeId("Or", "lex", k); k += 1
            nodes.append(n); real[n] = sym
            dom[n] = {"word": word, "morph": i, "cycle": cycle[i], "kind": m[1],
                      "red": 0, "base": int(m[1] == "stem" and red is not None), "L": int("L" in flags)}
    corr = {n: (n,) for n in nodes}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom, corr=corr)


def syllables(syms):
    live = [(j, s) for j, s in enumerate(syms) if s is not ABSENT]
    out = []
    for k, (j, s) in enumerate(live):
        if is_v(s):
            coda = k + 1 < len(live) and not is_v(live[k + 1][1]) and (k + 2 >= len(live) or not is_v(live[k + 2][1]))
            out.append((j, is_long(s) or coda))
    return out


def footings(weights, hl_feet: bool = True):
    n = len(weights)
    out = []
    def rec(i, acc):
        if i == n:
            out.append(tuple(acc)); return
        rec(i + 1, acc + ["u"])
        if weights[i]:
            rec(i + 1, acc + ["h"])
        if i + 1 < n and not (weights[i] and weights[i + 1]) and (hl_feet or not (weights[i] and not weights[i + 1])):
            rec(i + 2, acc + ["h", "w"])
    rec(0, [])
    return out


def wellformed(syms):
    live = [s for s in syms if s is not ABSENT]
    if not live or is_v(live[0]):
        return False
    run = 0
    for j, s in enumerate(live):
        if is_v(s):
            if j + 1 < len(live) and is_v(live[j + 1]):
                return False
            run = 0
        else:
            run += 1
            if run == 1 and j == 0 and j + 1 < len(live) and not is_v(live[j + 1]):
                return False
            if run >= 3:
                return False
            if j + 1 < len(live) and not is_v(live[j + 1]) and live[j + 1].rstrip("'") == s.rstrip("'") and j + 2 < len(live):
                return False
            coda = j + 1 >= len(live) or not is_v(live[j + 1])
            if coda and s.endswith("'") and j + 1 < len(live):
                return False
    return True


def candidates(ref: Struct, morphs, made_cycle: str = "own", max_copy: int = 5, truncate: bool = False, hl_feet: bool = True):
    cycle, red = info(morphs)
    nodes = list(ref.order["seg"])
    stem_nodes = [n for n in nodes if ref.dom[n]["kind"] == "stem"]
    stem_final = stem_nodes[-1] if stem_nodes and is_v(ref.real[stem_nodes[-1]]) else None
    after = [n for n in nodes if ref.dom[n]["morph"] > red] if red is not None else []
    ins = nodes.index(after[0]) if after else len(nodes)
    copy_lengths = [0] if red is None else sorted({*range(1, min(max_copy, len(stem_nodes)) + 1), len(stem_nodes)})
    for k in copy_lengths:
        copied = stem_nodes[:k]
        long_opts = [(True, False) if is_long(ref.real[b]) else (False,) for b in copied]
        for lengths in itertools.product(*long_opts):
            made = [NodeId("Or", "made", j) for j in range(k)]
            corr = {n: (n,) for n in nodes}
            for r, b in zip(made, copied):
                corr[r] = (b,)
            order = tuple(nodes[:ins] + made + nodes[ins:])
            dom = dict(ref.dom)
            for r, b in zip(made, copied):
                dom[r] = {"word": ref.dom[b]["word"], "morph": red, "kind": "red", "red": 1, "base": 0, "L": 0,
                          "cycle": cycle[red] if made_cycle == "own" else ref.dom[b]["cycle"]}
            base_real = {r: (ref.real[b] if lg else shorten(ref.real[b])) for r, b, lg in zip(made, copied, lengths)}
            for trunc in ((False, True) if truncate and 0 < k < len(stem_nodes) else (False,)):
              if trunc:
                base_real = dict(base_real)
                for b in stem_nodes[k:]:
                    base_real[b] = ABSENT
              vnodes = [n for n in order if is_v(base_real.get(n, ref.real.get(n)))]
              opts = []
              for j, n in enumerate(vnodes):
                  sym = base_real.get(n, ref.real.get(n))
                  o = [sym]
                  if is_long(sym) and n not in base_real:
                      o.append(shorten(sym))
                  elif n == stem_final:
                      nxt = order[order.index(n) + 1] if order.index(n) + 1 < len(order) else None
                      if nxt is not None and is_v(ref.real.get(nxt, base_real.get(nxt))):
                          o = [ABSENT]
                  elif not is_long(sym) and j > 0 and n not in base_real:
                      o.append(ABSENT)
                  opts.append(o)
              for choice in itertools.product(*opts):
                  real = {}
                  for n in order:
                      real[n] = base_real.get(n, ref.real.get(n))
                  for n, v in zip(vnodes, choice):
                      real[n] = v
                  syms = [real[n] for n in order]
                  if not wellformed(syms):
                      continue
                  syl = syllables(syms)
                  for ft in footings([h for _, h in syl], hl_feet):
                      r2 = dict(real)
                      for (j, _), st in zip(syl, ft):
                          n = order[j]
                          r2[n] = restress(real[n], st == "h", st != "u")
                      yield Struct(order={"seg": order}, real=r2, dom=dom, corr=corr)


def surface(s: Struct, stress: bool = True) -> str:
    out = []
    for n in s.order["seg"]:
        r = s.real[n]
        if r is ABSENT:
            continue
        out.append(r if (stress or not is_v(r)) else quality(r) + ("ː" if is_long(r) else ""))
    return "".join(out)


class _CoordIs(Term):
    def __init__(self, slot, coord, value): self.slot, self.coord, self.value = slot, coord, value
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        v = ctx.state.dom.get(o, ctx.reference.dom.get(o, {})).get(self.coord)
        return None if v is None else v == self.value
    def depth(self): return 1


T = Slot("t", "Or", "subject", kind="anchor")
N1 = Slot("n1", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=+1, filter="present")
N2 = Slot("n2", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=+1, filter="present", of="n1", tier="seg")
P1 = Slot("p1", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=-1, filter="present")
PV = Slot("pv", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=-1, filter="nuclear")
C = Slot("c", "Or", "subject", kind="corr", direction=+1, scope=WORD)
K = Slot("k", "Or", "subject", kind="corr", direction=-1, scope=WORD)
NEXT_RED_V = Slot("nrv", "Or", "subject", kind="search", scope=WORD, direction=+1, filter="nuclear", coord=(("red", 1),))

nuc = lambda s: Feat("nuclear", s, True)
cons = lambda s: Feat("nuclear", s, False)
long_ = lambda s: Feat("long", s, True)
stressed = lambda s: Feat("stressed", s, True)
parsed = lambda s: Feat("parsed", s, True)
CODA_T = And((Resolves("n1"), cons("n1"), Or_((Not(Resolves("n2")), cons("n2")))))
HEAVY_T = Or_((long_("t"), CODA_T))
CODA_C = Not(And((Resolves("n1"), nuc("n1"))))
red = lambda s: _CoordIs(s, "red", 1)


NV = Slot("nv", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=+1, filter="nuclear")
N3 = Slot("n3", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=+1, filter="present", of="n2", tier="seg")
SUPERHEAVY_T = Or_((And((long_("t"), CODA_T)),
                    And((CODA_T, Resolves("n2"), cons("n2"), Or_((Not(Resolves("n3")), cons("n3")))))))


def declarations(exceptional: str = "swp_listed", ident_br_side: str = "copy", foot_hl: bool = False,
                 superheavy: bool = False) -> dict:
    D = {}
    if superheavy:
        D["NO_3MU"] = Decl("NO_3MU", "Or", (T, N1, N2, N3), nuc("t"), Not(SUPERHEAVY_T), scope=WORD)
    if foot_hl:
        weak_nv = And((Resolves("nv"), Feat("parsed", "nv", True), Feat("stressed", "nv", False)))
        D["FOOT_HL"] = Decl("FOOT_HL", "Or", (T, N1, N2, NV), And((nuc("t"), stressed("t"))), Not(And((HEAVY_T, weak_nv))), scope=WORD)
    D["PARSE"] = Decl("PARSE", "Or", (T,), nuc("t"), parsed("t"), scope=WORD)
    D["WSP"] = Decl("WSP", "Or", (T, N1, N2), And((nuc("t"), HEAVY_T)), stressed("t"), scope=WORD)
    D["SWP"] = Decl("SWP", "Or", (T, N1, N2), And((nuc("t"), stressed("t"))), HEAVY_T, scope=WORD)
    D["NOLONGV"] = Decl("NOLONGV", "Or", (T,), nuc("t"), Not(long_("t")), scope=WORD)
    D["NOCODA"] = Decl("NOCODA", "Or", (T, N1), And((Present("t"), cons("t"))), Not(CODA_C), scope=WORD)
    D["MAX_V"] = Decl("MAX_V", "Or", (T,), Feat("nuclear", "t", True, where="reference"), Present("t"), kind="faithfulness",
                      locus_side="reference")
    D["MAX_C"] = Decl("MAX_C", "Or", (T,), Feat("nuclear", "t", False, where="reference"), Present("t"), kind="faithfulness",
                      locus_side="reference")
    D["IDENT_LEN"] = Decl("IDENT_LEN", "Or", (T,), And((Feat("nuclear", "t", True, where="reference"), Present("t"))),
                          SameFeat("long", ("t", "current"), ("t", "reference")), kind="faithfulness", locus_side="reference")
    D["DEP_BR"] = Decl("DEP_BR", "Or", (T, C), And((red("t"), Present("t"))), And((Resolves("c"), Present("c"))),
                       kind="faithfulness")
    D["MAX_BR"] = Decl("MAX_BR", "Or", (T, K), And((_CoordIs("t", "base", 1), Present("t"))),
                       And((Resolves("k"), Present("k"))), kind="faithfulness")
    if ident_br_side == "copy":
        D["IDENT_BR_LEN"] = Decl("IDENT_BR_LEN", "Or", (T, C), And((red("t"), nuc("t"), Resolves("c"), Present("c"))),
                                 SameFeat("long", ("t", "current"), ("c", "current")), kind="faithfulness")
    else:
        D["IDENT_BR_LEN"] = Decl("IDENT_BR_LEN", "Or", (T, K), And((_CoordIs("t", "base", 1), nuc("t"), Present("t"), Resolves("k"), Present("k"))),
                                 SameFeat("long", ("t", "current"), ("k", "current")), kind="faithfulness")
    D["NOCODA_RED"] = Decl("NOCODA_RED", "Or", (T, N1), And((red("t"), Present("t"), cons("t"))), Not(CODA_C), scope=WORD)
    D["NOLONGV_RED"] = Decl("NOLONGV_RED", "Or", (T,), And((red("t"), nuc("t"))), Not(long_("t")), scope=WORD)
    D["AFFIX_SYL_RED"] = Decl("AFFIX_SYL_RED", "Or", (T, NEXT_RED_V), And((red("t"), nuc("t"))), Not(Resolves("nrv")), scope=WORD)
    O = Slot("o", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=-1, filter="present")
    if exceptional == "swp_listed":
        member_L = Or_((_CoordIs("t", "L", 1), And((Resolves("o"), cons("o"), _CoordIs("o", "L", 1))),
                        And((CODA_T, _CoordIs("n1", "L", 1)))))
        D["SWP_L"] = Decl("SWP_L", "Or", (T, N1, N2, O), And((nuc("t"), stressed("t"), member_L)), HEAVY_T, scope=WORD)
    elif exceptional == "sync_listed":
        prev_light = And((Resolves("pv"), Not(long_("pv")), Not(And((Resolves("p1"), cons("p1"), Or_((Not(Resolves("pv")), TRUE)))))))
        ctx_left = And((Resolves("pv"), Not(long_("pv")), _PrevOpen("t")))
        D["SYNC_L"] = Decl("SYNC_L", "Or", (T, PV, P1), And((_CoordIs("t", "L", 1), nuc("t"), Not(long_("t")), ctx_left)),
                           Or_((Not(ctx_left), Not(Present("t")))), scope=WORD)
    elif exceptional == "sync_listed_retained":
        ctx_left = And((Resolves("pv"), Not(long_("pv")), _PrevOpen("t")))
        D["SYNC_L"] = Decl("SYNC_L", "Or", (T, PV, P1), And((_CoordIs("t", "L", 1), nuc("t"), Not(long_("t")), ctx_left)),
                           Not(Present("t")), scope=WORD)
    elif exceptional == "dep_exempt":
        D["DEP_BR"] = Decl("DEP_BR", "Or", (T, C), And((red("t"), Present("t"), Resolves("c"), Not(_CoordIs("c", "L", 1)))),
                           And((Resolves("c"), Present("c"))), kind="faithfulness")
    return D


class _PrevOpen(Term):
    def __init__(self, slot): self.slot = slot
    def slots(self): return frozenset({self.slot, "p1", "pv"})
    def eval(self, ctx):
        p1, pv = ctx.resolve("p1"), ctx.resolve("pv")
        if p1 is None or pv is None: return None
        live = [n for n in ctx.state.order["seg"] if ctx.sigma.present(ctx.state.real.get(n, ABSENT))]
        i, j = live.index(p1), live.index(pv)
        return i == j + 1
    def depth(self): return 1
