from dataclasses import replace
from fractions import Fraction
from itertools import product
import numpy as np
from . import frag_sandhi as native
from .core import And, Decl, Not, Or_, Resolves
from .evaluate import activation, coefficients
from .certificate import write

NAMES = ('S33','S11','S44','IDENT_REG','IDENT_CONT','IDENT_R','IDENT_FINAL','S32')
INPUTS = tuple(sorted({(a,b,t) for t in (1,3,4) for a in (2,3) for b in ((2,3) if t==3 else (3,t))}))
OUTPUTS = tuple(product((1,2,3,4),repeat=3))

def declarations(model):
    d=native.declarations()
    if model=='B':
        d['S33']=replace(d['S33'],consequence=native.tone('t',2))
    elif model=='C':
        ctx=And((Resolves('n'),native.tone('n',2)))
        d['S32']=Decl('S32','Syl',(native.T,native.N),And((native.tone('t',3),ctx)),
                      Or_((Not(ctx),native.tone('t',2))),scope=native.PHRASE)
    elif model!='A':
        raise ValueError(model)
    return d

def direct(u,v,model):
    a=np.zeros(8,dtype=int);b=a.copy()
    rules=[(0,3,3,2),(1,1,1,3),(2,4,4,3)]+([(7,3,2,2)] if model=='C' else [])
    for i in range(2):
        for j,target,trigger,out in rules:
            active=u[i]==target and u[i+1]==trigger
            current=v[i]==target and v[i+1]==trigger
            pressure=v[i]!=out and ((model=='B' and j==0) or v[i+1]==trigger)
            a[j]+=int(active and pressure)
            b[j]+=int(not active and current and pressure)
    a[3]=sum((x in (1,4))!=(y in (1,4)) for x,y in zip(u,v))
    a[4]=sum(x!=y for x,y in zip(u,v))
    a[5]=sum(u[i-1]==u[i] and u[i]!=v[i] for i in (1,2))
    a[6]=int(u[2]!=v[2])
    return a,b

def verify():
    records=[];gaps={};reader_checks=0
    for model in 'ABC':
        d=declarations(model)
        assert all(q.well_typed(native.SG)[0] for q in d.values())
        for u in INPUTS:
            ref=native.build([f'T{x}' for x in u]);act=activation(native.SG,ref,d)
            for v,c in zip(OUTPUTS,native.candidates(ref),strict=True):
                assert native.surface(c)==''.join(f'T{x}' for x in v)
                a,b=direct(u,v,model);cf=coefficients(native.SG,ref,c,d,act)
                for j,name in enumerate(NAMES):
                    if name in d:
                        assert cf[name]==(int(a[j]),int(b[j]))
                        reader_checks+=1
                records.append({'model':model,'input':u,'output':v,'old':a.tolist(),'new':b.tolist()})
        gaps[model]={}
        for u in [(3,3,3),(3,2,3)]:
            a,b=direct(u,(2,2,3),model);c,dn=direct(u,(3,2,3),model)
            gaps[model][''.join(map(str,u))]={'old':(a-c).tolist(),'new':(b-dn).tolist()}
    assert gaps['A']['333']==gaps['A']['323']=={'old':[0,0,0,0,1,0,0,0],'new':[0]*8}
    assert gaps['B']['333']=={'old':[-1,0,0,0,1,0,0,0],'new':[0]*8}
    assert gaps['C']['333']=={'old':[0,0,0,0,1,0,0,0],'new':[0,0,0,0,0,0,0,-1]}
    assert gaps['C']['323']=={'old':[0,0,0,0,1,0,0,-1],'new':[0]*8}
    noise=0
    for p,e in product([Fraction(i,20) for i in range(11)],repeat=2):
        assert e+(1-2*e)*p<=Fraction(1,2);noise+=1
    out={'inputs':len(INPUTS),'candidates_per_input':len(OUTPUTS),'models':3,
         'candidate_models':len(records),'coefficient_pairs_checked':reader_checks,
         'conditional_score_gaps':gaps,'symmetric_noise_instances':noise,'coefficients':records,
         'scope':'Finite source-informed tone fragment; equal base mass. B and C are comparison variants, not adopted changes. No independent planning/realization law or population inference.'}
    write('huaian_joint.json',out)
    print({k:v for k,v in out.items() if k!='coefficients'})

if __name__=='__main__':verify()
