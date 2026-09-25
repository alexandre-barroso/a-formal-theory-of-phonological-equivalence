
def run(data, work):
    from pathlib import Path
    from collections import defaultdict,Counter
    from dataclasses import replace
    from itertools import product
    import json,sys,math
    import numpy as np
    from scipy.special import xlogy

    O=Path(work)
    tokens=json.loads((O/'results/tokens_categorical.json').read_text())
    speakers=['1','3','4','5','6','8','9','10']
    alias={'wuxiguo':'wuxieguo','wuhugou':'wuhukou'}
    targets=[r for r in tokens if r['speaker'] in speakers and r['quality']=='good' and r['ur'] in ['333','323'] and r['sr'] in ['223','323']]
    frames=sorted({alias.get(r['frame'],r['frame']) for r in targets})
    n=np.zeros((8,6,2),int);k=n.copy()
    for r in targets:
        i,j,c=speakers.index(r['speaker']),frames.index(alias.get(r['frame'],r['frame'])),['333','323'].index(r['ur'])
        n[i,j,c]+=1;k[i,j,c]+=r['sr']=='223'
    assert n.sum()==358 and k.sum()==233

    def fit(kk,nn,model,epsilon=0):
        a,b=kk/nn
        pooled=kk.sum()/nn.sum()
        if model=='A':a=b=min(pooled,.5)
        if model=='B':
            b=min(b,.5)
            if a<b:a=b=min(pooled,.5)
        if model=='C' and a>b:a=b=pooled
        return np.clip([a,b],epsilon,1-epsilon)

    def nll(kk,nn,p):return float(-np.sum(xlogy(kk,p)+xlogy(nn-kk,1-p)))
    fits=[];nllsum=Counter()
    for i,s in enumerate(speakers):
        kk,nn=k[i].sum(0),n[i].sum(0)
        one={'speaker':s,'k':kk.tolist(),'n':nn.tolist(),'difference':float(kk[0]/nn[0]-kk[1]/nn[1]),'models':{}}
        for model in 'ABCR':
            p=fit(kk,nn,model);loss=nll(kk,nn,p);nllsum[model]+=loss
            one['models'][model]={'p':p.tolist(),'nll':loss,'finite_attainment':bool(np.all((p>0)&(p<1)))}
        fits.append(one)
    loo=[]
    for eps in [1e-6,.01,.05]:
        losses={model:np.zeros((8,6)) for model in 'ABCR'}
        for i in range(8):
            for j in range(6):
                trk,trn=k[i].sum(0)-k[i,j],n[i].sum(0)-n[i,j]
                assert np.all(trn>0)
                for model in 'ABCR':losses[model][i,j]=nll(k[i,j],n[i,j],fit(trk,trn,model,eps))
        loo.append({'epsilon':eps,'models':{m:{'nll':float(x.sum()),'nll_per_token':float(x.sum()/n.sum()),'participant_nll':x.sum(1).tolist(),'frame_nll':x.sum(0).tolist()} for m,x in losses.items()},
            'B_vs_C_per_participant':(losses['B'].sum(1)-losses['C'].sum(1)).tolist(),
            'B_vs_R_per_participant':(losses['B'].sum(1)-losses['R'].sum(1)).tolist()})
    rng=np.random.default_rng(20260920)
    boots=[]
    for _ in range(20000):
        ii=rng.integers(8,size=8);jj=rng.integers(6,size=6)
        kk=k[np.ix_(ii,jj)].sum((0,1));nn=n[np.ix_(ii,jj)].sum((0,1))
        boots.append(float(kk[0]/nn[0]-kk[1]/nn[1]))


    from phonological_requirements import frag_sandhi as native
    from phonological_requirements.evaluate import activation,coefficients
    from phonological_requirements.core import Decl,And,Or_,Not,Resolves
    names=['S33','S11','S44','IDENT_REG','IDENT_CONT','IDENT_R','IDENT_FINAL','S32']
    cs=list(product((1,2,3,4),repeat=3))
    def direct(u,v,model):
        a=np.zeros(8,int);b=a.copy();reg={1:0,2:1,3:1,4:0}
        for i in range(3):
            for j,before,trigger,after in [(0,3,3,2),(1,1,1,3),(2,4,4,3)]+([(7,3,2,2)] if model=='C' else []):
                active=i<2 and u[i]==before and u[i+1]==trigger
                current=i<2 and v[i]==before and v[i+1]==trigger
                pressure=i<2 and v[i]!=after and (True if model=='B' and j==0 else v[i+1]==trigger)
                a[j]+=active and pressure;b[j]+=not active and current and pressure
            a[3]+=reg[u[i]]!=reg[v[i]];a[4]+=u[i]!=v[i]
            a[5]+=i>0 and u[i-1]==u[i] and u[i]!=v[i];a[6]+=i==2 and u[i]!=v[i]
        return a,b
    checks=0;contrasts={}
    inputs=sorted({tuple(map(int,r['ur'])) for r in tokens if r['ur'] is not None})
    assert len(inputs)==12
    for model in 'BC':
        D=native.declarations()
        if model=='B':D['S33']=replace(D['S33'],consequence=native.tone('t',2))
        else:
            ctx=And((Resolves('n'),native.tone('n',2)))
            D['S32']=Decl('S32','Syl',(native.T,native.N),And((native.tone('t',3),ctx)),Or_((Not(ctx),native.tone('t',2))),scope=native.PHRASE)
        for d in D.values():assert d.well_typed(native.SG)[0]
        for u in inputs:
            U=native.build([f'T{x}' for x in u]);act=activation(native.SG,U,D)
            for v,cand in zip(cs,native.candidates(U)):
                a,b=direct(u,v,model);actual=coefficients(native.SG,U,cand,D,act)
                assert all(actual[name]==(int(a[j]),int(b[j])) for j,name in enumerate(names) if name in D)
                checks+=1
        contrasts[model]={}
        for u in [(3,3,3),(3,2,3)]:
            a,b=direct(u,(2,2,3),model);c,d=direct(u,(3,2,3),model)
            contrasts[model][''.join(map(str,u))]={'old_difference':(a-c).tolist(),'new_difference':(b-d).tolist()}
    assert contrasts['B']['333']['old_difference']==[-1,0,0,0,1,0,0,0]
    assert contrasts['B']['323']['old_difference']==[0,0,0,0,1,0,0,0]
    assert contrasts['C']['333']['new_difference']==[0,0,0,0,0,0,0,-1]
    assert contrasts['C']['323']['old_difference']==[0,0,0,0,1,0,0,-1]
    result={'source':'Original annotations; retrospective joint test','frames':frames,'alias_from_source_Table4':alias,
     'n':n.tolist(),'k':k.tolist(),'paired_speaker_results':fits,'total_conditional_nll':dict(nllsum),
     'leave_one_frame_out':loo,'joint_difference':143/182-90/176,
     'crossed_bootstrap95':list(map(float,np.quantile(boots,[.025,.975]))),'bootstrap_replicates':20000,
     'native_variant_candidates':checks,'contrasts':contrasts,
     'limits':'Conditional likelihood families exactly characterized, not full64-grammar MLEs. Source R benchmark only licenses compatible categorical probabilities; it is not an implemented planning model. All fits retrospective; epsilon sensitivities predeclared before per-speaker323 results.'}
    (O/'results/joint.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['n','k']},indent=2))
