
def run(data,work):
    from pathlib import Path
    from itertools import product
    from collections import Counter
    import json, ast, hashlib, time
    import numpy as np
    from scipy.optimize import minimize, check_grad
    from scipy.special import logsumexp

    O=Path(work)
    from .huaian_joint import direct
    tokens=json.loads((O/'results/tokens_categorical.json').read_text())
    speakers=['1','3','4','5','6','8','9','10'];candidates=list(product(range(1,5),repeat=3))
    inputs=sorted({tuple(map(int,r['ur'])) for r in tokens if r['ur']})
    selected=[r for r in tokens if r['speaker'] in speakers and r['quality']=='good' and r['sr']]
    assert len(selected)==2192 and len(inputs)==12
    assert Counter(r['process'] for r in selected)=={'1':731,'3':726,'4':735}
    process_of={r['ur']:r['process'] for r in selected}
    Y={s:np.zeros((12,64)) for s in speakers}
    for r in selected:Y[r['speaker']][inputs.index(tuple(map(int,r['ur']))),candidates.index(tuple(map(int,r['sr'])))]+=1
    coef={m:np.array([[direct(u,v,m) for v in candidates] for u in inputs],float)[:,:,:,:7 if m!='C' else 8] for m in 'ABC'}

    def objective(x,y,ab):
        a,b=ab[:,:,0,:],ab[:,:,1,:];w,l=x[:-1],x[-1]
        f=a+l*b;score=f@w;lp=-score-logsumexp(-score,axis=1)[:,None]
        p=np.exp(lp);res=y-y.sum(1)[:,None]*p
        return float(-np.sum(y*lp)),np.r_[np.einsum('ij,ijk->k',res,f),np.sum(res*(b@w))]

    gradient=[]
    for m in 'ABC':
        rng=np.random.default_rng(20260920)
        x=np.r_[rng.uniform(.2,3,size=coef[m].shape[-1]),.4]
        e=check_grad(lambda z:objective(z,Y['1'],coef[m])[0],lambda z:objective(z,Y['1'],coef[m])[1],x)
        gradient.append({'model':m,'absolute_l2_error':e});assert e<1e-3

    fits=[];runs=[];start=time.monotonic()
    for cap in [60,90]:
      for s in speakers:
        for m in 'ABC':
          npar=coef[m].shape[-1];bounds=[(0,cap)]*npar+[(0,1)]
          rr=[]
          for level in [2,4]:
            for lam in [.1,.4,.8]:
              w=np.full(npar,level,float);w[0]=6 if level==2 else 15;w[6]=20 if level==2 else 30
              x0=np.r_[w,lam]
              opt=minimize(lambda x:objective(x,Y[s],coef[m]),x0,jac=True,method='L-BFGS-B',bounds=bounds,options={'ftol':1e-13,'gtol':1e-8,'maxiter':3000,'maxls':80})
              f,g=objective(opt.x,Y[s],coef[m]);pg=g.copy()
              for j,(lo,hi) in enumerate(bounds):
                if opt.x[j]<=lo+1e-7 and g[j]>0:pg[j]=0
                if opt.x[j]>=hi-1e-7 and g[j]<0:pg[j]=0
              r={'speaker':s,'model':m,'cap':cap,'start_level':level,'start_lambda':lam,'x':opt.x.tolist(),'nll':f,'success':bool(opt.success),'message':str(opt.message),'iterations':int(opt.nit),'projected_gradient':float(np.max(np.abs(pg)))}
              r['passed']=r['success'] and r['projected_gradient']<=1e-4;rr.append(r);runs.append(r)
          best=min(rr,key=lambda r:r['nll'])
          if not best['passed']:
            original=dict(best); extra=[]
            for method in ['L-BFGS-B','SLSQP']:
              options={'ftol':0.,'gtol':1e-9,'maxiter':5000,'maxls':100} if method=='L-BFGS-B' else {'ftol':1e-12,'maxiter':2000}
              opt=minimize(lambda x:objective(x,Y[s],coef[m]),np.array(original['x']),jac=True,bounds=bounds,method=method,options=options)
              value,refinement_gradient=objective(opt.x,Y[s],coef[m]);pg=refinement_gradient.copy()
              for j,(lo,hi) in enumerate(bounds):
                if opt.x[j]<=lo+1e-7 and pg[j]>0:pg[j]=0
                if opt.x[j]>=hi-1e-7 and pg[j]<0:pg[j]=0
              extra.append(dict(original,x=opt.x.tolist(),nll=value,success=bool(opt.success),message=str(opt.message),projected_gradient=float(np.max(abs(pg))),passed=bool(opt.success and max(abs(pg))<=1e-4),method=method))
            acceptable=[a for a in extra if a['passed']]
            if acceptable:best=min(acceptable,key=lambda a:a['nll'])
            best=dict(best,convergence_history={'original':original,'refinements':extra})
          x=np.array(best['x']);a,b=coef[m][:,:,0,:],coef[m][:,:,1,:];sc=(a+x[-1]*b)@x[:-1];lp=-sc-logsumexp(-sc,axis=1)[:,None]
          groups=[]
          for j,u in enumerate(inputs):
            groups.append({'input':''.join(map(str,u)),'n':int(Y[s][j].sum()),'counts':Y[s][j].astype(int).tolist(),'probability':np.exp(lp[j]).tolist(),'nll':float(-Y[s][j]@lp[j])})
          best=dict(best,groups=groups,process_nll={str(t):sum(g['nll'] for g in groups if process_of[g['input']]==str(t)) for t in [1,3,4]},start_range=[min(z['nll'] for z in rr),max(z['nll'] for z in rr)],near_best_starts=sum(z['nll']-best['nll']<1e-5 for z in rr))
          fits.append(best)
          print(json.dumps({k:v for k,v in best.items() if k not in ['groups','x']}),flush=True)
    result={'selected_tokens':len(selected),'gradient_checks':gradient,'candidates':[''.join(map(str,c)) for c in candidates],'inputs':[''.join(map(str,u)) for u in inputs],'fits':fits,'starts':runs,'seconds':time.monotonic()-start,'numerical_protocol':{'starts':6,'caps':[60,90],'gradient_tolerance':1e-4,'refinement':'L-BFGS-B and SLSQP only if selected fit misses tolerance'},'interpretation':'Retrospective complete candidate control fits; local optimization is not proof of global optimality.'}
    (O/'results/allprocess.json').write_text(json.dumps(result,indent=2)+'\n')
    summary={'selected_fits':len(fits),'starts':len(runs),'passed_selected':sum(f['passed'] for f in fits),'seconds':result['seconds'],'totals':{str(cap):{m:{'nll':sum(f['nll'] for f in fits if f['cap']==cap and f['model']==m),'process_nll':{str(t):sum(f['process_nll'][str(t)] for f in fits if f['cap']==cap and f['model']==m) for t in [1,3,4]},'failed_speakers':[f['speaker'] for f in fits if f['cap']==cap and f['model']==m and not f['passed']]} for m in 'ABC'} for cap in [60,90]}}
    (O/'results/allprocess_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
