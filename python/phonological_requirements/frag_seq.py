from __future__ import annotations

import itertools

from .core import (ABSENT, And, Decl, Feat, NodeId, Not, Or_, Present, RelDecl,
                   Resolves, Scope, Sigma, Slot, SortDecl, Struct, TRUE)

WORD = Scope(same=("word",), label="word")
T = Slot("t", "Or", "subject", kind="anchor")
LEFT_1 = Slot("l1", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=-1, filter="present", policy="dynamic")
LEFT_2 = Slot("l2", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=-1, filter="present", of="l1", tier="seg")
RIGHT_1 = Slot("r1", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=+1, filter="present", policy="dynamic")
RIGHT_2 = Slot("r2", "Or", "subject", kind="stepof", relation="succ", scope=WORD, direction=+1, filter="present", of="r1", tier="seg")


def make_sigma(alphabet: dict) -> Sigma:
    classes = sorted({c for cs in alphabet.values() for c in cs})
    f = {}
    for s, cs in alphabet.items():
        f[s] = {"present": True, "sym": s, **{"is_" + c: (c in cs) for c in classes}}
    f[ABSENT] = {"present": False, "sym": None, **{"is_" + c: None for c in classes}}
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"), "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=f, default_features={"present": True, "sym": None, **{"is_" + c: False for c in classes}},
                 domains=("word",))


def _ctx_term(slots_, spec):
    parts = []
    for slot, c in zip(slots_, spec):
        if c == "#":
            parts.append(Not(Resolves(slot)))
        else:
            parts.append(And((Resolves(slot), Feat("is_" + c, slot, True))))
    return And(tuple(parts)) if parts else TRUE


MODES = ("discharge", "retain", "ltr", "rtl")


def context_slots(scope=WORD):
    return (Slot("l1", "Or", "subject", kind="step", relation="succ", scope=scope, direction=-1, filter="present", policy="dynamic"),
            Slot("l2", "Or", "subject", kind="stepof", relation="succ", scope=scope, direction=-1, filter="present", of="l1", tier="seg"),
            Slot("r1", "Or", "subject", kind="step", relation="succ", scope=scope, direction=+1, filter="present", policy="dynamic"),
            Slot("r2", "Or", "subject", kind="stepof", relation="succ", scope=scope, direction=+1, filter="present", of="r1", tier="seg"))


def rule_decl(name, target, left, right, out, mode, scope=WORD):
    if len(left) > 2 or len(right) > 2:
        raise ValueError("the sequence fragment supports at most two context slots per side")
    if mode not in MODES:
        raise ValueError(f"unknown rule mode {mode!r}")
    lt, rt = _ctx_term(("l1", "l2"), left), _ctx_term(("r1", "r2"), right)
    ctx = And((lt, rt))
    repair = Not(Present("t")) if out is None else Feat("sym", "t", out)
    act = And((Feat("is_" + target, "t", True), ctx))
    carried = {"discharge": ctx, "retain": None, "ltr": lt, "rtl": rt}[mode]
    cons = repair if carried is None or carried is TRUE else Or_((Not(carried), repair))
    slots_ = (T, LEFT_1, LEFT_2, RIGHT_1, RIGHT_2) if scope is WORD else (T,) + context_slots(scope)
    return Decl(name, "Or", slots_, act, cons, scope=scope)


def faith_decls(alphabet, changes):
    D = {}
    for a, b in changes:
        if b is None:
            D[f"MAX_{a}"] = Decl(f"MAX_{a}", "Or", (T,), Feat("is_" + a, "t", True, where="reference"), Present("t"),
                                 kind="faithfulness")
        else:
            D[f"IDENT_{a}_{b}"] = Decl(f"IDENT_{a}_{b}", "Or", (T,), Feat("is_" + a, "t", True, where="reference"),
                                       Or_((Not(Present("t")), Feat("sym", "t", None) if False else Not(Feat("sym", "t", b)))),
                                       kind="faithfulness")
    return D


def build(symbols) -> Struct:
    nodes, real, dom = [], {}, {}
    for i, s in enumerate(symbols):
        n = NodeId("Or", "lex", i); nodes.append(n); real[n] = s; dom[n] = {"word": 0}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom)


def candidates(ref: Struct, options):
    nodes = ref.order["seg"]
    per = [options.get(ref.real[n], [ref.real[n]]) for n in nodes]
    for combo in itertools.product(*per):
        yield Struct(order=ref.order, real=dict(zip(nodes, combo)), dom=ref.dom)


def surface(s: Struct) -> str:
    return "".join(s.real[n] for n in s.order["seg"] if s.real[n] != ABSENT)
