from __future__ import annotations

import sys
from itertools import product

RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def kernel(f, domain):
    return {(x, y) for x in domain for y in domain if f(x) == f(y)}


def blocks(f, domain):
    out: dict = {}
    for x in domain:
        out.setdefault(f(x), []).append(x)
    return sorted(tuple(sorted(v)) for v in out.values())


order1, order2 = ("a", "b", "c"), ("a", "c", "b")
check("carrier: the winner query returns a for both analyses",
      order1[0] == order2[0] == "a")
check("carrier: the complete-order query separates the two analyses", order1 != order2)
check("carrier eq:rep-query-factor: the winner factors through the complete order "
      "(erase every position but the first) but not conversely",
      (lambda g: g(order1) == g(order2))(lambda o: o[0])
      and len({order1, order2}) == 2)

DOMAIN = ("a", "b", "c")
Q1 = {"a": 0, "b": 0, "c": 1}
Q2 = {"a": 0, "b": 1, "c": 1}
check("eq:rep-running-q1: Q1 partitions the domain as {{a,b},{c}}",
      blocks(Q1.__getitem__, DOMAIN) == [("a", "b"), ("c",)],
      str(blocks(Q1.__getitem__, DOMAIN)))
price = sum(len({Q2[x] for x in block}) - 1 for block in blocks(Q1.__getitem__, DOMAIN))
check("eq:rep-running-price: adding Q2 costs exactly one further carrier cell",
      price == 1, str(price))
attained = sorted({(Q1[x], Q2[x]) for x in DOMAIN})
check("carrier: the product carrier for (Q1, Q2) attains exactly (0,0), (0,1), (1,1)",
      attained == [(0, 0), (0, 1), (1, 1)], str(attained))
check("carrier: the merger a,b -> [a,b] is one cell too coarse for the product request",
      len(blocks(Q1.__getitem__, DOMAIN)) + price == len(attained))

check("eq:rep-product-kernel-intersection: ker(Q1,Q2) = ker Q1 ∩ ker Q2",
      kernel(lambda x: (Q1[x], Q2[x]), DOMAIN)
      == kernel(Q1.__getitem__, DOMAIN) & kernel(Q2.__getitem__, DOMAIN))
check("thm:rep-fin-a4: a factoring weaker query has a coarser kernel; "
      "adding a consumer can only refine",
      kernel(lambda x: (Q1[x], Q2[x]), DOMAIN) <= kernel(Q1.__getitem__, DOMAIN)
      and kernel(lambda x: (Q1[x], Q2[x]), DOMAIN) != kernel(Q1.__getitem__, DOMAIN))

ROWS = {"a": (0, 1), "b": (1, 0)}
merge = {"a": "u", "b": "u"}
check("eq:rep-universal-neutral-rows: a constant winner query survives the merger "
      "while 'is C1 zero?' does not",
      len({0 for _ in ROWS}) == 1
      and len({ROWS[x][0] == 0 for x in ROWS}) == 2
      and len({merge[x] for x in ROWS}) == 1)
for size in range(1, 5):
    dom = tuple(range(size))
    for images in product(range(size), repeat=size):
        r = dict(zip(dom, images))
        injective = len(set(images)) == size
        every_binary_factors = all(
            all(r[x] != r[y] or b[x] == b[y] for x in dom for y in dom)
            for b in (dict(zip(dom, bits)) for bits in product((0, 1), repeat=size)))
        if injective != every_binary_factors:
            check("eq:rep-universal-query-injectivity fails", False, f"{size} {images}")
            break
check("eq:rep-universal-query-injectivity: r is injective iff every binary query "
      "factors through it, over all reductions on domains of size <= 4", True)

F = {"a": "u", "b": "u", "c": "v"}
G = {"u": "w", "v": "w"}
dom = ("a", "b", "c")
coll_f = {(x, y) for x in dom for y in dom if x != y and F[x] == F[y]}
coll_gf = {(x, y) for x in dom for y in dom if x != y and G[F[x]] == G[F[y]]}
new = {(x, y) for x in dom for y in dom if x != y and F[x] != F[y] and G[F[x]] == G[F[y]]}
check("eq:rep-collision-decomposition: Coll(g∘f) = Coll(f) ⊍ New(f,g), disjointly",
      coll_gf == coll_f | new and not (coll_f & new),
      f"{sorted(coll_gf)} vs {sorted(coll_f)} ⊍ {sorted(new)}")
check("carrier: the fixture collides a,b at the first stage and newly collides each with c",
      coll_f == {("a", "b"), ("b", "a")}
      and new == {("a", "c"), ("c", "a"), ("b", "c"), ("c", "b")})

q = {"a": 0, "b": 0, "c": 0, "d": 1}
Fop = {"a": "c", "b": "d"}
check("carrier: q(a) = q(b) = 0 permits the direct block {a,b}, but the context q(F[-]) splits it",
      q["a"] == q["b"] and q[Fop["a"]] != q[Fop["b"]])

partial = {"a": "c"}
readout = {x: ("some", q[partial[x]]) if x in partial else ("none",) for x in ("a", "b")}
check("eq:rep-option-readout: definedness separates a and b even though both have q = 0",
      q["a"] == q["b"] and readout["a"] != readout["b"], str(readout))
check("carrier: dropping the undefined row would retrospectively change the question's domain",
      set(readout) == {"a", "b"} and "b" not in partial)


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} query and carrier claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
