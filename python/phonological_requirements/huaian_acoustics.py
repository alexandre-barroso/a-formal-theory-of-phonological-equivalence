
def run(data, work):
    from pathlib import Path
    from collections import defaultdict, Counter
    import csv,json,hashlib
    import numpy as np

    O=Path(work);source=Path(data)/'Measurements on the First Syllable Using Z-Scored Pitch/Exp4T2Data.csv'
    assert hashlib.sha256(source.read_bytes()).hexdigest()=='afdcf502a362b57bc8b1b656592f458b54d6b0761a0123e55943777cfa2b4eba'
    roots={'wufushen','wuxiguo','wuxieguo','wuhugou','wuhukou','wuyishen','wufuxu','wumaiguo'}
    speakers=['1','3','4','5','6','8','9','10']
    groups=defaultdict(list)
    with source.open(encoding='utf-8-sig') as f:
        for r in csv.DictReader(f):groups[tuple(r[k] for k in ['speaker','startTime','endTime','word'])].append(r)
    t=np.linspace(-1,1,21)
    Q=np.linalg.qr(np.column_stack((np.ones(21),t,t*t)))[0]
    for j in range(3):
        if np.dot(Q[:,j],np.column_stack((np.ones(21),t,t*t))[:,j])<0:Q[:,j]*=-1
    records=[];flow=Counter();annot=Counter()
    for key,rows in groups.items():
        assert sorted(int(r['step']) for r in rows)==list(range(21))
        r=rows[0]
        if r['speaker'] not in speakers or r['quality']!='good' or r['word'][:-1] not in roots:continue
        first=r['word'][-1];current=r['toneSandhiCurrent'];after=r['toneSandhiAfter']
        annot[(first,current,after)]+=1
        if first=='2' and current=='none' and after=='none':condition='control2';label=1
        elif first=='3' and current=='no' and after=='none':condition='control3';label=0
        elif first=='3' and current in ['yes','no'] and after=='yes':condition='target';label=int(current=='yes')
        else:continue
        y=[];inds=[]
        for row in rows:
            try:v=float(row['pitch'])
            except ValueError:continue
            if not np.isfinite(v) or v<=0:continue
            inds.append(int(row['step']));y.append(np.log(v))
        if len(y)<18:flow[condition+'_excluded_less18steps']+=1;continue
        beta=np.linalg.lstsq(Q[inds],y,rcond=None)[0]
        records.append(dict(speaker=r['speaker'],frame=r['word'][:-1],word=r['word'],start=r['startTime'],end=r['endTime'],condition=condition,label=label,valid_steps=len(y),coef=beta.tolist()))
        flow[condition+'_included']+=1
    X=np.array([r['coef'] for r in records]);Z=np.zeros_like(X)
    cal=np.array([r['condition']!='target' for r in records]);target=~cal
    Y=np.array([r['label'] for r in records])
    for s in speakers:
        mask=np.array([r['speaker']==s for r in records]);train=mask&cal
        assert len(set(Y[train]))==2
        mu=X[train].mean(0);sd=X[train].std(0,ddof=1);assert np.all(sd>0)
        Z[mask]=(X[mask]-mu)/sd
    means=[Z[cal&(Y==y)].mean(0) for y in (0,1)]
    res=np.concatenate([Z[cal&(Y==y)]-means[y] for y in (0,1)])
    cov=res.T@res/(cal.sum()-2)
    results=[]
    for ridge in [.05,.01,.2]:
        W=np.linalg.solve(cov+ridge*np.trace(cov)/3*np.eye(3),means[1]-means[0])
        score=(Z-(means[0]+means[1])/2)@W;pred=(score>=0).astype(int)
        result={'ridge':ridge,'target_n':int(target.sum()),'agreement':float(np.mean(pred[target]==Y[target])),
                'target_confusion':{f'label{y}_prediction{p}':int(np.sum(target&(Y==y)&(pred==p))) for y in (0,1) for p in (0,1)},
                'calibration_accuracy_NOT_holdout':float(np.mean(pred[cal]==Y[cal])),
                'speaker_results':[]}
        for s in speakers:
            mask=np.array([r['speaker']==s for r in records])&target
            result['speaker_results'].append({'speaker':s,'n':int(mask.sum()),'agreement':float(np.mean(pred[mask]==Y[mask])),
                'mean_score_label2':float(score[mask&(Y==1)].mean()) if np.any(mask&(Y==1)) else None,
                'mean_score_label3':float(score[mask&(Y==0)].mean()) if np.any(mask&(Y==0)) else None})
        results.append(result)
        if ridge==.05:
            for i,r in enumerate(records):r['score']=float(score[i]);r['prediction']=int(pred[i])
    out={'quadratic_logHz_LDA':{'minimum_finite_positive_steps':18,'control_only_scaling':True,'equal_priors':True,'ridge_primary':.05,'ridge_sensitivities':[.01,.2]},'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'all_token_blocks':len(groups),'annotations':{'|'.join(k):v for k,v in annot.items()},'flow':dict(flow),
         'results':results,'interpretation':'Secondary acoustic agreement check only; not independently measured categorical error rates or grammar probabilities.'}
    (O/'results/acoustic_records.json').write_text(json.dumps(records,indent=2)+'\n')
    (O/'results/acoustic_summary.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
