from __future__ import annotations

import itertools
from fractions import Fraction as F
from . import certificate
from .continuous import objective_x,profile,reach,solve_quadratic


def original(h,weights,values):
    previous=F(1)
    total=F(0)
    for weight,x in zip(weights,values):
        total+=h*max(previous-x,0)**2+weight*x
        previous=x
    return total


def running_minimum(values):
    previous=F(1)
    result=[]
    for x in values:
        previous=min(previous,x)
        result.append(previous)
    return result


def main():
    comparisons=two_site=zero_site=zero_suffix=negative=0
    grid=[F(k,4) for k in range(5)]
    records=[]
    for n in range(1,4):
        for weights in itertools.product([F(0),F(1),F(2)],repeat=n):
            for h in [F(1),F(5),F(100)]:
                optimal=profile(h,weights)
                d=solve_quadratic(h,weights)
                cumulative=reach(weights)
                assert all(v>=0 for v in d) and sum(d)<=1
                mu=F(0) if sum(d)<1 else max((cumulative[i]-2*h*d[i] for i in range(n) if d[i]>0),default=F(0))
                assert mu>=0 and mu*(1-sum(d))==0
                assert all(d[i]==max(cumulative[i]-mu,0)/(2*h) for i in range(n))
                optimum=original(h,weights,optimal[1:])
                for xs in itertools.product(grid,repeat=n):
                    v=original(h,weights,xs)
                    assert v==objective_x(h,weights,2,[F(1),*xs])
                    assert v>=optimum
                    assert original(h,weights,running_minimum(xs))<=v
                    comparisons+=1
                if weights[-1]==0 and any(weights):
                    changed=[*optimal[1:-1],F(1)]
                    assert changed!=optimal[1:] and original(h,weights,changed)==optimum
    for c in [F(k,8) for k in range(17)]:
        minimum=c-c*c/4
        for x,y in itertools.product([F(k,16) for k in range(17)],repeat=2):
            v=original(F(1),[c,F(0)],[x,y])
            assert v==minimum+(x-(1-c/2))**2+max(x-y,0)**2
            assert (v==minimum)==(x==1-c/2 and x<=y)
            two_site+=1
    for n in range(33):
        assert profile(F(5),[F(0)]*n)==[F(1)]*(n+1)
        assert original(F(5),[F(0)]*n,[F(1)]*n)==0
        zero_site+=1
    for h,weights in [(F(1),[F(2)]),(F(100),[F(1)]*4),(F(1),[F(0)]*2)]:
        base=profile(h,weights)
        for length in range(9):
            extended=profile(h,[*weights,*([F(0)]*length)])
            assert extended[:len(base)]==base
            assert extended[len(base):]==[base[-1]]*length
            zero_suffix+=1
        records.append({'h':str(h),'weights':list(map(str,weights)),'canonical_profile':list(map(str,base))})
    for x in [F(k,64) for k in range(65)]:
        value=original(F(1),[F(-1)],[x])
        assert value>=-1 and (value==-1)==(x==1)
        negative+=1
    assert comparisons>10000 and two_site==4913 and zero_site==33 and zero_suffix==27 and negative==65
    result={'original_grid_comparisons':comparisons,'two_site_argmin_checks':two_site,
            'all_zero_horizons':zero_site,'zero_cost_suffix_checks':zero_suffix,
            'negative_single_site_checks':negative,'extension_records':records,
            'two_site_family':{'h':1,'p':2,'weights':['c',0],'domain':'0<=c<=2;0<=x,y<=1','minimizers':'x=1-c/2 and x<=y<=1','minimum':'c-c^2/4'},
            'scope':'Unique reduced optimizer is separate from original-cube minimizers. Nonnegative sites do not ensure a first zero; arbitrary negative sites do not force every conclusion to fail.'}
    certificate.write('heterogeneous_boundary.json',result)
    print(comparisons,'original-cube checks;',two_site,'two-site argmin checks;',zero_site,'zero-cost horizons;',zero_suffix,'zero-cost suffixes;',negative,'negative-site controls')


if __name__=='__main__':main()
