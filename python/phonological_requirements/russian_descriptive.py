from pathlib import Path
import json
import sys
import numpy as np
from .certificate import write


def contrast(rows,mask,positive,negative):
    rr=[r for r,t in zip(rows,mask) if t];y=np.array([[int(r['accept.faithful']),int(r['accept.deletion'])] for r in rr]);a=positive[mask];b=negative[mask]
    ps=sorted({r['userCode'] for r in rr});cs=sorted({r['cluster'] for r in rr});pi={v:i for i,v in enumerate(ps)};ci={v:i for i,v in enumerate(cs)}
    ix=np.array([pi[r['userCode']]*len(cs)+ci[r['cluster']] for r in rr]);shape=(len(ps),len(cs))
    def cell(values):return np.bincount(ix,weights=values,minlength=len(ps)*len(cs)).reshape(shape)
    na=np.stack([cell(y[:,j]*a) for j in [0,1]]);nb=np.stack([cell(y[:,j]*b) for j in [0,1]]);da=cell(a.astype(int));db=cell(b.astype(int))
    gen=np.random.default_rng(2026092001);samples=[]
    for _ in range(2000):
        p=gen.multinomial(len(ps),np.ones(len(ps))/len(ps));c=gen.multinomial(len(cs),np.ones(len(cs))/len(cs));mult=p[:,None]*c[None,:];ad=np.sum(mult*da);bd=np.sum(mult*db)
        if ad and bd:samples.append(np.sum(mult[None,:,:]*na,axis=(1,2))/ad-np.sum(mult[None,:,:]*nb,axis=(1,2))/bd)
    return {'positive_trials':int(a.sum()),'negative_trials':int(b.sum()),'faithful_deletion_rate_difference':(y[a].mean(axis=0)-y[b].mean(axis=0)).tolist(),'interval95_faithful_deletion':np.quantile(samples,[.025,.975],axis=0).T.tolist(),'resamples':len(samples),'participants':len(ps),'clusters':len(cs)}


def main(work):
    rows=json.loads((work/'response_rows.json').read_text());shape=np.array(['CVC' if r['C']=='2' else ('CVCC' if r['position']=='1' else 'CCVC') for r in rows]);tr=np.array([r['type'] in ['TR','RTR','TTR'] for r in rows]);out=[]
    for split,mask in [('all_targets',np.ones(len(rows),bool)),('primary_test',np.array([r['person_test'] and r['cluster_test'] for r in rows]))]:
        for name,a,b in [('CVCC_minus_CVC',shape=='CVCC',shape=='CVC'),('TR_minus_other',tr,~tr)]:out.append({'split':split,'contrast':name,**contrast(rows,mask,a,b)})
    record={'effects':out,'scope':'Marginal descriptive differences; crossed participant/cluster resampling with paired responses; not causal effects or a reproduction of the source mixed-effects coefficients.','seed':2026092001}
    write('russian_descriptive.json',record,work);print(json.dumps(record))

if __name__=='__main__':main(Path(sys.argv[1]))
