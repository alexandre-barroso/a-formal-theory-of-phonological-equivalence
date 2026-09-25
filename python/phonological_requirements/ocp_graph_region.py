from __future__ import annotations

import itertools
from dataclasses import replace
from fractions import Fraction as F
from . import certificate, frag_ocp as O
from .core import ABSENT, read
from .evaluate import activation, coefficients, score


def candidates():
    return itertools.product((False, True), repeat=6)


def independent_coefficients(c):
    p, q, e00, e01, e10, e11 = c
    return (2-int(p)-int(q), 2-int(e00)-int(e11),
            int(p and q and e00 and e11), int(p and q and e01 and e10))


def build(c):
    p, q, *edges = c
    s = O.build(('H' if p else ABSENT, 'H' if q else ABSENT), {0:None, 1:None})
    tones, bearers = s.nodes('tone'), s.nodes('seg')
    assoc = frozenset((tones[i], bearers[j]) for (i, j), present in
                      zip(itertools.product(range(2), repeat=2), edges) if present)
    return replace(s, assoc=assoc)


def main():
    sigma = O.make_sigma()
    assert all(r.source in sigma.sorts and r.target in sigma.sorts and
               r.instance_sort in sigma.sorts for r in sigma.relations.values())
    assert all(d.well_typed(sigma)[0] for d in O.DECLS.values())
    ref = O.build(('H','H'), {0:0, 1:1})
    acts = activation(sigma, ref, O.DECLS)
    cs = list(candidates())
    states = [build(c) for c in cs]
    expected = [independent_coefficients(c) for c in cs]
    native = []
    rows = []
    for c, s, (d, k, old, new) in zip(cs, states, expected):
        assert s.well_formed(ref)[0]
        observed = coefficients(sigma, ref, s, O.DECLS, acts)
        assert observed == {'PARSE-T':(d,0), 'PARSE-A':(k,0), 'OCP':(old,new)}
        rs = [read(sigma,ref,s,O.OCP,n,'tone').triple() for n in s.nodes('tone')]
        assert [int(a and e and not q) for a,e,q in rs] == [old,new]
        native.append(observed)
        rows.append({'candidate':c,'coefficients':[d,k,old,new],'ocp_readers':rs,'display':O.describe(s)})
    assert len(cs)==64 and len({O.describe(s) for s in states})==64
    reference_pairs = 0
    for reference, qr in zip(states, expected):
        act = activation(sigma, reference, {'OCP':O.OCP})
        for s, qs in zip(states, expected):
            observed = coefficients(sigma, reference, s, {'OCP':O.OCP}, act)['OCP']
            expected_pair = (sum(qr[i+2]*qs[i+2] for i in range(2)),
                             sum((1-qr[i+2])*qs[i+2] for i in range(2)))
            assert observed == expected_pair
            reference_pairs += 1
    grid = 0
    values = (F(0), F(1,8), F(1), F(2), F(40))
    for t,a,w,lam in itertools.product(values,repeat=4):
        costs = [d*t+k*a+old*w+new*lam*w for d,k,old,new in expected]
        assert costs == [score(q, {'PARSE-T':t,'PARSE-A':a,'OCP':w}, lam) for q in native]
        m = min(costs)
        assert m == min(t,a,w)
        winners = [i for i,v in enumerate(costs) if v==m]
        assert all(expected[i][2:]==(0,0) for i in winners) == (min(t,a)<w and min(t,a)<a+lam*w)
        grid += 1
    assert reference_pairs==4096 and grid==625
    record = {'candidates':rows,'reference_candidate_pairs':reference_pairs,'grid_cases':grid,
              'minimum':'min(w,t,a)','exact_region':'min(t,a)<w and min(t,a)<a+lambda*w',
              'scope':'Two ordered tone origins, two fixed bearers, four independent association edges; edges at absent origins retained. No productive-span, fusion or full Myers translation claim.'}
    certificate.write('ocp_graph_region.json', record)
    print(f'{len(cs)} candidates; {reference_pairs} reference/candidate checks; {grid} exact weight cases')


if __name__ == '__main__':
    main()
