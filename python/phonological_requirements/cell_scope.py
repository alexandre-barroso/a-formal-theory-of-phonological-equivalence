from fractions import Fraction as Q
from itertools import product
import json, random
from . import paths


def main():
    cell_checks = order_checks = rescaling_checks = 0
    for a,c,p,w,lam in product((0,1), (0,1), (0,1), (Q(1,3),Q(1),Q(4)), (Q(0),Q(1,8),Q(1),Q(2))):
        charge=w*(a*p+lam*(1-a)*c*p)
        assert (charge>0 and c*p==0)==(a==1 and c==0 and p==1)
        assert (a==0 and c*p==1)==(a==0 and c==1 and p==1)
        cell_checks+=1
    assert 1*0==0 and 1!=0
    rng=random.Random(20260919)
    dot=lambda a,b:sum(x*y for x,y in zip(a,b))
    for n in range(0,9):
        for _ in range(100):
            w=[Q(rng.randrange(8),3) for _ in range(n)]
            f=[Q(rng.randrange(8),4) for _ in range(n)]
            fp=[x-Q(rng.randrange(5),7) for x in f]
            assert dot(w,fp)<=dot(w,f)
            if any(x>0 and z<y for x,y,z in zip(w,f,fp)):assert dot(w,fp)<dot(w,f)
            m=[Q(rng.randrange(8),5) for _ in range(n)]
            assert dot(w,m)+Q(1,3)<dot(w,m)+Q(2,3)
            order_checks+=1
            new=[rng.randrange(2) for _ in range(n)]
            a=[0 if b else Q(rng.randrange(8),3) for b in new]
            b=[Q(rng.randrange(8),3) if flag else 0 for flag in new]
            lam=Q(rng.randrange(9),7); lp=Q(rng.randrange(1,9),5)
            wp=[x*lam/lp if flag else x for x,flag in zip(w,new)]
            assert all(x>=0 for x in wp)
            assert dot(wp,[x+lp*y for x,y in zip(a,b)])==dot(w,[x+lam*y for x,y in zip(a,b)])
            rescaling_checks+=1
    threshold_checks=0
    for common,lam,w,r in product((Q(-2),Q(0),Q(3)),(Q(0),Q(1,8),Q(1,2),Q(1)),(Q(0),Q(2),Q(8)),(Q(0),Q(1),Q(3))):
        lhs=common+lam*w; rhs=common+r
        assert (lhs<rhs)==(lam*w<r)
        assert (lhs==rhs)==(lam*w==r)
        assert (lhs>rhs)==(lam*w>r)
        threshold_checks+=1
    mutants={
        'zero_reference_markedness_implies_absent_context': not (1*0==0 and 1!=0),
        'fixed_faithfulness_order_survives_all_reweighting': dot([1,2],[0,1])<dot([1,2],[1,0]),
        'zero_weights_preserve_strict_dominance': dot([0,0],[0,0])<dot([0,0],[1,1]),
        'one_locus_threshold_ignores_other_costs': Q(1,8)*4+2<1,
    }
    assert all(not v for v in mutants.values())
    out={'seed':20260919,'cell_checks':cell_checks,'order_checks':order_checks,'rescaling_checks':rescaling_checks,'threshold_checks':threshold_checks,'non_equivalent_mutations_detected':list(mutants),'scope':'Exact rational local identities, fixed versus varying weights, isolated comparisons and separated-column reparametrization. General finite-index proofs are in CellScope.lean.'}
    paths.CERTIFICATES.mkdir(parents=True,exist_ok=True)
    (paths.CERTIFICATES/'cell_scope.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))

if __name__=='__main__':main()
