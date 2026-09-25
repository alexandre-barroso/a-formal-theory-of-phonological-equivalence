from __future__ import annotations

import itertools
from dataclasses import replace
from math import comb
from . import certificate
from .core import ABSENT, read
from .evaluate import activation, coefficients
from .generate import closure, canonical
from .noninterference import ALPHABET, DECLS, build2, project, make_sigma

SET = ('a','t',ABSENT)
INSERT = ('n',)


def word_keys(ref, made):
    ns = tuple(ref.nodes('seg'))
    for slots in itertools.combinations(range(len(ns)+made),made):
        created = set(slots)
        for values in itertools.product(SET,repeat=len(ns)):
            for inserted in itertools.product(INSERT,repeat=made):
                lex_i=made_i=0; out=[]
                for i in range(len(ns)+made):
                    if i in created:
                        out.append(('made',made_i,inserted[made_i],tuple(sorted(ref.dom[ns[0]].items()))))
                        made_i+=1
                    else:
                        n=ns[lex_i]
                        out.append((n.kind,n.index,values[lex_i],tuple(sorted(ref.dom[n].items()))))
                        lex_i+=1
                yield tuple(out)


def combine(left,right):
    result=[];made=0
    for tag,index,value,dom in left+right:
        if tag=='made':index=made;made+=1
        result.append((tag,index,value,dom))
    return tuple(result)


def expected(ref,bound):
    words=[project(ref,w) for w in range(2)]
    parts=[[tuple(word_keys(word,k)) for k in range(bound+1)] for word in words]
    return {combine(a,b) for i in range(bound+1) for j in range(bound+1-i)
            for a in parts[0][i] for b in parts[1][j]}


def main():
    sigma=replace(make_sigma(ALPHABET),domains=('word','phrase'))
    records=[];reader_checks=coefficient_checks=0
    for words in [('a','a'),('a','at'),('at','ta'),('ata','t')]:
        ref=build2(words);refs=[project(ref,w) for w in range(2)]
        acts=activation(sigma,ref,DECLS);part_acts=[activation(sigma,u,DECLS) for u in refs]
        for bound in range(3):
            states=closure(ref,('set','insert'),SET,INSERT,bound)
            actual={canonical(s) for s in states}; independent=expected(ref,bound)
            assert actual==independent and len(actual)==len(states)
            count=sum(comb(len(words[0])+i,i)*comb(len(words[1])+j,j)
                      *len(SET)**sum(map(len,words))*len(INSERT)**(i+j)
                      for i in range(bound+1) for j in range(bound+1-i))
            assert len(actual)==count
            for state in states:
                combined=coefficients(sigma,ref,state,DECLS,acts)
                separated=[]
                for w in range(2):
                    local=project(state,w)
                    separated.append(coefficients(sigma,refs[w],local,DECLS,part_acts[w]))
                    for name,decl in DECLS.items():
                        for node in local.nodes('seg'):
                            a=read(sigma,ref,state,decl,node).triple()
                            b=read(sigma,refs[w],local,decl,node).triple()
                            assert a==b
                            reader_checks+=1
                assert all(combined[d]==tuple(separated[0][d][k]+separated[1][d][k] for k in range(2)) for d in DECLS)
                coefficient_checks+=1
            records.append({'words':words,'bound':bound,'native_canonical_structures':len(actual),'independent_count':count})
    ref=build2(('a','a'));states=closure(ref,('set','insert'),SET,INSERT,1)
    keys={canonical(s) for s in states};both_boundary=[]
    for word in (0,1):
        both_boundary.append(any(k[1][0]=='made' and dict(k[1][3])['word']==word for k in keys if len(k)==3))
    assert all(both_boundary)
                                                                                  
    w0,w1=project(ref,0),project(ref,1)
    excluded=combine(next(word_keys(w0,1)),next(word_keys(w1,1)))
    assert excluded not in keys and excluded in expected(ref,2)
    record={'cases':records,'reader_projection_checks':reader_checks,'complete_coefficient_projection_checks':coefficient_checks,
            'both_boundary_owners_present':both_boundary,'global_cutoff_counterexample_detected':True,
            'scope':'Independent interleaving enumeration compared with the native set/insert closure, modulo created-node renaming. Base declarations only; frozen activation and all old/new coefficients checked before weights.'}
    assert len(records)==12 and reader_checks>0 and coefficient_checks>0
    certificate.write('word_projection.json',record);print(record)


if __name__=='__main__':main()
