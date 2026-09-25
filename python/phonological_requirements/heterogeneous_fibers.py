from fractions import Fraction as F
from itertools import product, combinations
import json,random
from . import certificate
from .continuous import objective_x,profile,solve_quadratic

def original(h,m,x,p=2):
    return sum(h*max(a-b,F(0))**p for a,b in zip(x,x[1:]))+sum(a*b for a,b in zip(m,x[1:]))
def env(x):
    return tuple(min(x[:k+1]) for k in range(len(x)))
def drops(x):
    return tuple(max(a-b,F(0)) for a,b in zip(x,x[1:]))
def reduced(h,m,d,p=2):
    return sum(m)+sum(h*t**p for t in d)-sum(sum(m[i:])*t for i,t in enumerate(d))
def independent_optimizer(h,m):
    M=tuple(sum(m[i:]) for i in range(len(m)))
    all_mu={F(0)}
    for k in range(1,len(m)+1):
        for subset in combinations(range(len(m)),k):
            all_mu.add((sum(M[i] for i in subset)-2*h)/k)
    valid={}
    for mu in all_mu:
        if mu<0:continue
        d=tuple(max(v-mu,F(0))/(2*h) for v in M)
        if sum(d)<=1 and mu*(1-sum(d))==0:
            valid[d]=mu
    assert len(valid)==1,(h,m,valid)
    d,mu=next(iter(valid.items()))
    x=tuple(F(1)-sum(d[:i]) for i in range(len(d)+1))
    return x,d,mu
def main():
    counts={k:0 for k in ['systems','original_scores','envelope_inequalities','fiber_equivalences','simplex_identities','native_profile_matches','grid_minimizers','positive_weight_uniqueness','zero_horizons','long_fibers']}
    for n in range(5):
        for m in product([F(0),F(1),F(2)],repeat=n):
            for h in [F(1,2),F(3)]:
                canonical,d,mu=independent_optimizer(h,m)
                assert tuple(profile(h,m))==canonical
                assert tuple(solve_quadratic(h,m))==d
                counts['systems']+=1;counts['native_profile_matches']+=1
                optimum=original(h,m,canonical)
                assert optimum==reduced(h,m,d)
                assert mu>=0 and sum(d)<=1 and mu*(1-sum(d))==0
                for rest in product([F(0),F(1,2),F(1)],repeat=n):
                    x=(F(1),*rest);r=env(x);dr=drops(r)
                    e=original(h,m,x);er=original(h,m,r)
                    assert e==objective_x(h,m,2,x)
                    assert er<=e and optimum<=e
                    assert er==reduced(h,m,dr)
                    fiber=(r==canonical and drops(x)==d and all(w==0 or a==b for w,a,b in zip(m,x[1:],canonical[1:])))
                    assert (e==optimum)==fiber,(m,x,canonical)
                    counts['original_scores']+=1;counts['envelope_inequalities']+=1;counts['fiber_equivalences']+=1;counts['simplex_identities']+=1
                    if e==optimum:
                        counts['grid_minimizers']+=1
                        if all(w>0 for w in m):
                            assert x==canonical;counts['positive_weight_uniqueness']+=1
    for n in range(33):
        x=(F(1),)*(n+1);m=(F(0),)*n
        assert original(F(1),m,x)==0 and tuple(profile(F(1),m))==x
        counts['zero_horizons']+=1
    rng=random.Random(20260920)
    for n in [5,10,25,50]:
        for _ in range(25):
            m=tuple(F(rng.randrange(4)) for i in range(n-1))+(F(0),)
            h=F(rng.randrange(1,100),3)
            canonical=tuple(profile(h,m));x=canonical[:-1]+(F(1),)
            assert original(h,m,x)==original(h,m,canonical)
            assert drops(x)==drops(canonical) and env(x)==canonical
            counts['long_fibers']+=1
    assert counts['systems']==242 and counts['original_scores']==14762
    record={'counts':counts,'seed':20260920}
    certificate.write('heterogeneous_fibers.json',record)
    print(json.dumps(record))

if __name__ == "__main__": main()
