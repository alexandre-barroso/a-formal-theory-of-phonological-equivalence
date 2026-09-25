from pathlib import Path
import sys
from itertools import product
from fractions import Fraction as F
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from phonological_equivalence.order_comparison import order, winners, normalized
from phonological_requirements import certificate, paths
from phonological_requirements.indep_gua import Product, WEIGHTS, MARKEDNESS
from phonological_opacity.gua.grammar import INPUTS_SELECTION, GRAMMAR
from phonological_opacity.gua.model import Model
from phonological_opacity.gua.check_selection import counts, scores


def main():
    profiles={'a':(0,0),'b':(0,1),'c':(1,0)}
    source=order(profiles,(0,1)); target=order(profiles,(1,0))
    changed=source ^ target
    canonical={tuple(sorted(p)) for p in changed}
    assert source=={('a','b'),('a','c'),('b','c')}
    assert target=={('a','b'),('a','c'),('c','b')}
    assert winners(profiles,source)==winners(profiles,target)=={'a'}
    assert changed=={('b','c'),('c','b')} and canonical=={('b','c')}
    first=normalized({'a':4,'b':2,'c':1}); second=normalized({'a':16,'b':4,'c':1})
    assert all((first[x]<first[y])==(second[x]<second[y]) for x,y in product(profiles,repeat=2))
    assert first!=second and sum(first.values())==sum(second.values())==1
    restricted=normalized({'a':4,'b':2})
    assert winners(('a','b'),source)=={'a'} and restricted['a']!=first['a']
    u=next(u for u in INPUTS_SELECTION if u['id']=='G34a')
    prod=Product(u['id'],[x['phone'] for x in u['slots']],[x['word'] for x in u['slots']],u['phrases'],u['focal'])
    native=Model(GRAMMAR,u); activation=prod.activation_bits(); rows=[]
    for i in (566,774,605):
        state=native.expand(native.states[i]); co=prod.coefficients(state,activation)
        terms=[F(w)*(a+F(1,8)*b) for w,(a,b) in zip(WEIGHTS,co)]
        parts=[sum(terms[k] for k in range(9) if k not in MARKEDNESS),terms[4],terms[5],sum(terms)]
        nc=counts(native,state)
        assert all(list(co[k])==nc[k][2:4] for k in range(9))
        assert scores(nc)[1]==8*parts[-1]
        C,D,G=prod.readers(state)
        current=[sum(C[k][q] and D[k][q] and not G[k][q] for q in range(prod.n)) for k in MARKEDNESS]
        rows.append({'index':i,'surface':prod.observe(state),'parts':[str(x) for x in parts],'current':current})
    assert [r['parts'] for r in rows]==[['0','4','8','12'],['3','0','0','3'],['2','4','0','6']]
    assert rows[1]['current']==rows[2]['current']==[0,0,0,0]
    record={'order_source':sorted(source),'order_target':sorted(target),'changed_directed':sorted(changed),'changed_canonical':sorted(canonical),'winner':['a'],'laws':[{k:str(v) for k,v in law.items()} for law in (first,second,restricted)],'gua_rows':rows,'profile_comparisons':18,'gua_native_coefficient_pairs':27,'status':'PASS'}
    certificate.write('opening_comparisons.json',record,paths.REPO/'results/finite')
    print('PASS: 18 ordered comparisons, 27 native Gua coefficient pairs, all three opening rows, two full laws and deletion law')
    return 0


if __name__=='__main__':raise SystemExit(main())
