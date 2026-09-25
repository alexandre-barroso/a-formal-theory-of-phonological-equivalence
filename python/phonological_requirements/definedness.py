from __future__ import annotations

import itertools
from . import certificate, core as C, frag_apocope as A, strictness


def main():
    truth=(False,None,True)
    values={False:-1,None:0,True:1};inverse={-1:False,0:None,1:True}
    pairs=0
    for a,b in itertools.product(truth,repeat=2):
        assert C.k_and(a,b) is inverse[min(values[a],values[b])]
        assert C.k_or(a,b) is inverse[max(values[a],values[b])]
        assert C.k_not(a) is inverse[-values[a]]
        pairs+=1
    sigma=A.sigma();ref=A.struct(['a','t']);locus=ref.nodes('seg')[0]
    missing=C.Slot('n','Rel','subject',kind='step',relation='succ',scope=A.WORD,direction=-1)
    atom=C.Feat('nuclear','n',True)
    terms={'true_or_missing':C.Or_((C.TRUE,atom)),
           'false_and_missing':C.And((C.FALSE,atom)),
           'property_of_missing':atom,
           'exists_and_property':C.And((C.Resolves('n'),atom))}
    expected={'true_or_missing':((True,True,True),0,True),
              'false_and_missing':((True,True,False),1,False),
              'property_of_missing':((True,False,False),0,True),
              'exists_and_property':((True,True,False),1,False)}
    records={}
    for name,term in terms.items():
        decl=C.Decl(name,'Or',(A.T,missing),C.TRUE,term,scope=A.WORD)
        assert decl.well_typed(sigma)[0]
        assert C.Ctx(sigma,ref,ref,decl,locus).resolve('n') is None
        readers=C.read(sigma,ref,ref,decl,locus)
        certified=strictness.subject_strict(decl,'n')[0]
        assert (readers.triple(),readers.pressure,certified)==expected[name]
        records[name]={'well_typed':True,'missing_slot':'n','readers':readers.triple(),'pressure':readers.pressure,'subject_strict':certified}
    assert pairs==9 and len(records)==4
    record={'truth_pairs':pairs,'native_declarations':records,'scope':'No definedness override; native Kleene semantics and pressure-strictness tested independently of absence of truth value.'}
    certificate.write('definedness.json',record);print(record)


if __name__=='__main__':main()
