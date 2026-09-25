from __future__ import annotations

import itertools
from fractions import Fraction as F
from . import certificate, frag_ocp as O
from .core import ABSENT, read
from .evaluate import activation, coefficients, score


def candidates():
    return itertools.product((False, True), (False, True), (0, 1, None), (0, 1, None))


def independent_coefficients(c):
    p, q, i, j = c
    return (int(not p)+int(not q), int(i != 0)+int(j != 1),
            int(p and q and i == 0 and j == 1),
            int(p and q and i == 1 and j == 0))


def independent_score(c, t, a, w, lam):
    d, k, old, new = independent_coefficients(c)
    return d*t+k*a+old*w+new*lam*w


def good(c):
    p, q, i, j = c
    return not (p and q and ((i == 0 and j == 1) or (i == 1 and j == 0)))


def main():
    sigma = O.make_sigma(); ref = O.build(('H','H'), {0:0,1:1})
    acts = activation(sigma, ref, O.DECLS)
    rows=[]
    for c in candidates():
        p,q,i,j=c
        s=O.build(('H' if p else ABSENT,'H' if q else ABSENT),{0:i,1:j})
        assert s.well_formed(ref)[0]
        d,k,old,new=independent_coefficients(c)
        native=coefficients(sigma,ref,s,O.DECLS,acts)
        assert native == {'PARSE-T':(d,0),'PARSE-A':(k,0),'OCP':(old,new)},(c,native)
        readers=[read(sigma,ref,s,O.OCP,n,'tone').triple() for n in s.nodes('tone')]
        assert [int(x[0] and x[1] and not x[2]) for x in readers]==[old,new]
        rows.append({'candidate':c,'coefficients':[d,k,old,new],'ocp_readers':readers})
    grid=0; invariant=0
    values=(F(0),F(1,8),F(1),F(2),F(40))
    for t,a,w,lam in itertools.product(values,repeat=4):
        costs=[independent_score(c,t,a,w,lam) for c in candidates()]
        m=min(costs); threshold=min(t,a)
        assert m==min(w,threshold)
        selected=[c for c,v in zip(candidates(),costs) if v==m]
        assert all(good(c) for c in selected)==(threshold<w and threshold<2*a+lam*w)
        if w>threshold:
            changed=[independent_score(c,t,a,w+7,lam) for c in candidates()]
            assert selected==[c for c,v in zip(candidates(),changed) if v==min(changed)]
            invariant+=1
        grid+=1
    assert len(rows)==36 and grid==625
    rec={'candidates':rows,'grid_cases':grid,'above_threshold_pairs':invariant,
         'minimum':'min(w,t,a)','exact_region':'w>min(t,a) and 2a+lambda*w>min(t,a)',
         'weight_invariance':'Complete minimizers invariant for fixed nonnegative t,a,lambda when both OCP weights exceed min(t,a).',
         'scope':'Two tones/two bearers, 36 containment structures; no fusion, new-association penalty, directional head constraint or full Myers GEN translation.'}
    certificate.write('ocp_region.json',rec)
    print(f'{len(rows)} native candidate/readers/coefficient bridges; {grid} weight cases; {invariant} threshold invariance pairs')


if __name__=='__main__':main()
