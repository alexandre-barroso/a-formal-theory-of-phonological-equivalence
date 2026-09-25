from __future__ import annotations

import itertools
from fractions import Fraction
from . import certificate


def reachable(edges, start):
    seen = {start}
    pending = [start]
    while pending:
        source = pending.pop()
        for a,b in edges:
            if a == source and b not in seen:
                seen.add(b); pending.append(b)
    return seen


def relations():
    pairs = tuple(itertools.product(range(2),repeat=2))
    return [frozenset(p for k,p in enumerate(pairs) if mask & (1<<k)) for mask in range(16)]


def argmin(domain, score):
    if not domain: return set()
    value = min(map(score,domain))
    return {x for x in domain if score(x)==value}


def main():
    closures = minimizers = 0
    states = tuple(itertools.product(range(2),repeat=2))
    weights = list(itertools.product((-1,0,1),repeat=2))
    for ra,rb in itertools.product(relations(),repeat=2):
        edges = {(p,q) for p in states for q in states
                 if (p[0],q[0]) in ra and p[1]==q[1]
                 or p[0]==q[0] and (p[1],q[1]) in rb}
        for a,b in states:
            da,db = reachable(ra,a),reachable(rb,b)
            domain = reachable(edges,(a,b))
            assert domain == set(itertools.product(da,db))
            closures += 1
            for f,g in itertools.product(weights,repeat=2):
                joint = argmin(domain,lambda p:f[p[0]]+g[p[1]])
                separate = set(itertools.product(argmin(da,lambda x:f[x]),argmin(db,lambda x:g[x])))
                assert joint==separate
                minimizers+=1
    assert closures==1024 and minimizers==82944
    empty_cases=0
    for da,db in itertools.product([set(),{0},{1},{0,1}],repeat=2):
        f=lambda x:Fraction(x,3)
        g=lambda x:Fraction(1-x,5)
        assert argmin(set(itertools.product(da,db)),lambda p:f(p[0])+g(p[1]))==set(itertools.product(argmin(da,f),argmin(db,g)))
        empty_cases+=1
    mutants={
        'allow_joint_change':reachable({((0,0),(1,1))},(0,0)) != {(0,0)},
        'discard_ties':argmin(set(states),lambda p:0) != {(0,0)},
        'nonadditive_score':argmin(set(states),lambda p:-int(p==(1,1))) != set(states),
        'global_cutoff_is_product':{p for p in states if sum(p)<=1} != set(states)}
    assert all(mutants.values())
    record={'relation_pairs':256,'reachable_product_cases':closures,'all_minimizer_cases':minimizers,
            'including_empty_domain_cases':empty_cases,'signed_integer_scores':[-1,0,1],
            'mutation_controls':mutants,'scope':'Finite independent checks of universal arbitrary-relation and real-additive-score theorems; native regional generator and reader locality require separate bridges.'}
    certificate.write('product_composition.json',record);print(record)


if __name__=='__main__':main()
