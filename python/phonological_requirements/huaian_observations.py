
def run(data, work):
    from pathlib import Path
    from collections import Counter, defaultdict
    from itertools import product
    import csv, hashlib, json, math, sys
    import numpy as np
    from scipy.special import logsumexp
    from scipy.stats import binomtest

    O = Path(work); S = Path(data)
    source = S / 'Measurements on the Crucial Second Syllable Using Z-Scored Pitch/Exp4Data.csv'
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    assert sha(source) == '03258a374ecb466a65c03335c88fb1e61bcc4aa4968fe340b7f2df3ad23788ec'
    names = {'1': {'wubache', 'wubaxia', 'wugufen', 'wubaoshu', 'wubaoche', 'wubaixia'},
             '4': {'wubaoshui', 'wuduorou', 'wubamai', 'wudaixiang', 'wubupao', 'wujurou'},
             '3': {'wufushen', 'wuxiguo', 'wuxieguo', 'wuhugou', 'wuhukou', 'wuyishen', 'wufuxu', 'wumaiguo'}}

    def blocks(path):
        out = defaultdict(list)
        with path.open(encoding='utf-8-sig') as f:
            for r in csv.DictReader(f):
                out[tuple(r[k] for k in ('speaker', 'startTime', 'endTime', 'word'))].append(r)
        for key, rows in out.items():
            assert sorted(int(r['step']) for r in rows) == list(range(21)), key
            for k in rows[0]:
                if k not in ('pitch', 'step'):
                    assert len({r[k] for r in rows}) == 1, (key, k)
        return out

    raw = blocks(source)
    tokens = []
    for key, rows in raw.items():
        r = rows[0]
        proc = next((k for k, v in names.items() if r['word'][:-1] in v), None)
        b, c = r['toneSandhiBefore'], r['toneSandhiCurrent']
        ur = sr = None
        if proc is not None and b in ('none', 'yes', 'no') and c in ('none', 'yes', 'no'):
            second = r['word'][-1]
            first = '2' if b == 'none' else '3'
            ur = first + second + proc
            sr = ('2' if b == 'yes' else first) + ({'1': '3', '4': '3', '3': '2'}[second] if c == 'yes' else second) + proc
        tokens.append(dict(speaker=r['speaker'], frame=r['word'][:-1], word=r['word'],
                           start=r['startTime'], end=r['endTime'], process=proc,
                           quality=r['quality'], ur=ur, sr=sr))
    assert len(tokens) == 2882
    speakers = ['1', '3', '4', '5', '6', '8', '9', '10']

    def summarize(rows):
        ct = Counter((r['ur'], r['sr']) for r in rows if r['ur'] is not None)
        target = [r for r in rows if r['ur'] == '333' and r['sr'] in ('223', '323')]
        bysp, byframe = defaultdict(Counter), defaultdict(Counter)
        for r in target:
            bysp[r['speaker']][r['sr']] += 1
            byframe[r['frame']][r['sr']] += 1
        summaries = []
        for s, counts in sorted(bysp.items(), key=lambda x: int(x[0])):
            n, k = sum(counts.values()), counts['223']
            summaries.append(dict(speaker=s, n=n, k=k, proportion=k/n,
                                  binomial_p_conditional_iid=binomtest(k, n, .5, alternative='greater').pvalue))
        k, n = sum(r['sr'] == '223' for r in target), len(target)
        return dict(cells={a+'>'+b: v for (a,b),v in sorted(ct.items())},
                    target_n=n, target_k=k, target_proportion=k/n,
                    speakers=summaries,
                    frames={s:dict(c) for s,c in sorted(byframe.items())},
                    token_iid_p_NOT_cluster_inference=binomtest(k,n,.5,alternative='greater').pvalue,
                    minimum_label_changes_to_half=math.ceil(k-n/2),
                    corruption_fraction=max(0,k/n-.5),
                    minimum_asymmetric_FPR_minus_FNR=max(0,2*k/n-1))

    samples = {'primary_good8':[r for r in tokens if r['speaker'] in speakers and r['quality']=='good'],
               'good10':[r for r in tokens if r['quality']=='good'],
               'all_quality8':[r for r in tokens if r['speaker'] in speakers],
               'all_quality10':tokens}
    result = {s:summarize(rows) for s,rows in samples.items()}
    primary = samples['primary_good8']
    target = [r for r in primary if r['ur']=='333' and r['sr'] in ('223','323')]
    frames = sorted({r['frame'] for r in target})
    succ = np.zeros((len(speakers),len(frames)),int); trials=succ.copy()
    for r in target:
        i,j=speakers.index(r['speaker']),frames.index(r['frame'])
        trials[i,j]+=1;succ[i,j]+=int(r['sr']=='223')
    assert trials.sum()==182 and succ.sum()==143
    rng=np.random.default_rng(20260920)
    boot = {'participant':[], 'frame':[], 'crossed':[]}
    for _ in range(20000):
        ii=rng.integers(len(speakers),size=len(speakers));jj=rng.integers(len(frames),size=len(frames))
        boot['participant'].append(succ[ii].sum()/trials[ii].sum())
        boot['frame'].append(succ[:,jj].sum()/trials[:,jj].sum())
        boot['crossed'].append(succ[np.ix_(ii,jj)].sum()/trials[np.ix_(ii,jj)].sum())
    ci={k:list(map(float,np.quantile(v,[.025,.975]))) for k,v in boot.items()}
    means=succ.sum(1)/trials.sum(1)
    mean=float(means.mean());nn=len(means)
    hoeffding=math.exp(-2*nn*max(0,mean-.5)**2)
    kl=mean*math.log(2*mean)+(1-mean)*math.log(2*(1-mean))
    chernoff=math.exp(-nn*kl)
    result['uncertainty']={'bootstrap_seed':20260920,'bootstrap_replicates':20000,
        'percentile95':ci,'scope':'Descriptive secondary clustered bootstrap; convenience participants and few frames. No population-random-sample claim.',
        'participant_mean':mean,'bounded_independent_participant_Hoeffding':hoeffding,
        'bounded_independent_participant_Chernoff':chernoff,
        'bound_assumptions':'If conditional per-participant sample proportions are independent bounded variables with each mean<=.5, allowing arbitrary within-participant dependence. Null-mean condition is an additional sampling assumption for random conditional denominators.',
        'leave_one_participant_out':[{'omitted':s,'p':float((succ.sum()-succ[i].sum())/(trials.sum()-trials[i].sum()))} for i,s in enumerate(speakers)],
        'leave_one_frame_out':[{'omitted':s,'p':float((succ.sum()-succ[:,j].sum())/(trials.sum()-trials[:,j].sum()))} for j,s in enumerate(frames)]}
    unknown=[r for r in tokens if r['speaker'] in speakers and r['process']=='3' and r['word'].endswith('3') and r['ur'] is None]
    result['excluded_worst_case']={'unmappable_tokens_with_second_UR3':len(unknown),
       'include_every_such_token_as333_323':143/(182+len(unknown)),
       'additional_known_target_nonprimary':[r for r in samples['all_quality8'] if r['ur']=='333' and r['quality']!='good']}

    NAMES=['S33','S11','S44','IDENT_REG','IDENT_CONT','IDENT_R','IDENT_FINAL']
    REG={1:0,2:1,3:1,4:0}
    def coeff(u,v,mode='carried'):
        a=np.zeros(7,int);b=a.copy()
        for i in range(3):
            for j,t,out in [(0,3,2),(1,1,3),(2,4,3)]:
                active=i<2 and u[i]==t and u[i+1]==t
                current=i<2 and v[i]==t and v[i+1]==t
                pressure=i<2 and v[i]!=out and (v[i+1]==t if mode=='carried' or t!=3 else True)
                a[j]+=active and pressure;b[j]+=(not active) and current and pressure
            a[3]+=REG[u[i]]!=REG[v[i]];a[4]+=u[i]!=v[i]
            a[5]+=(i>0 and u[i-1]==u[i] and u[i]!=v[i])
            a[6]+=(i==2 and u[i]!=v[i])
        return a,b


    from phonological_requirements import frag_sandhi as native
    from phonological_requirements.evaluate import activation,coefficients
    from phonological_requirements.core import Decl
    cs=list(product((1,2,3,4),repeat=3))
    inputs=sorted({tuple(map(int,r['ur'])) for r in primary})
    assert len(inputs)==12
    checked=0
    native_records=[]
    for u in inputs:
        ref=native.build([f'T{x}' for x in u]);decl=native.declarations();acts=activation(native.SG,ref,decl)
        for v,c in zip(cs,native.candidates(ref)):
            assert native.surface(c)==''.join(f'T{x}' for x in v)
            a,b=coeff(u,v);actual=coefficients(native.SG,ref,c,decl,acts)
            assert all(actual[k]==(int(a[j]),int(b[j])) for j,k in enumerate(NAMES))
            native_records.append(dict(ur=u,sr=v,old=a.tolist(),new=b.tolist()))
            checked+=1
    assert checked==768
    a,b=coeff((3,3,3),(2,2,3));c,d=coeff((3,3,3),(3,2,3))
    assert list(a-c)==[0,0,0,0,1,0,0] and not np.any(b-d)
    tests=0
    for _ in range(200):
        w=rng.uniform(0,20,7);lam=rng.uniform(0,1)
        scores=np.array([(x+lam*y)@w for v in cs for x,y in [coeff((3,3,3),v)]])
        p=np.exp(-scores-logsumexp(-scores));q=p[cs.index((2,2,3))]/(p[cs.index((2,2,3))]+p[cs.index((3,2,3))])
        assert abs(q-1/(1+math.exp(w[4])))<1e-12
        tests+=1
    result['native_semantics']={'inputs':len(inputs),'candidates_per_input':64,'native_candidates_checked':checked,
        'native_coefficient_pairs_checked':checked*7,'old_223_minus_323':(a-c).tolist(),
        'new_223_minus_323':(b-d).tolist(),'full_law_checks':tests}
    (O/'results/native_coefficients.json').write_text(json.dumps(native_records,separators=(',',':'))+'\n')
    (O/'results/tokens_categorical.json').write_text(json.dumps(tokens,indent=2)+'\n')
    (O/'results/analysis.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
