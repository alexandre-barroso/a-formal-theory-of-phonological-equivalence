from pathlib import Path
from collections import defaultdict
from datetime import datetime, timezone
import argparse, csv, hashlib, json
import numpy as np

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('predictions', type=Path)
    ap.add_argument('--root-table', type=Path, required=True)
    ap.add_argument('--verified-result', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    assert not a.output.exists()
    verified = json.loads(a.verified_result.read_text())
    assert verified['predictions_sha256'] == digest(a.predictions)
    roots = {r['root']: r for r in csv.DictReader(a.root_table.open())}
    observed_keys = ['observed_'+s for s in ('unraised_old','unraised_opposite','raised_old','raised_opposite')]
    log_keys = ['log_predicted_'+s for s in ('unraised_old','unraised_opposite','raised_old','raised_opposite')]
    groups = defaultdict(lambda: defaultdict(list))
    max_odds_error = 0.; rows = 0; checked_odds = 0
    for r in csv.DictReader(a.predictions.open()):
        rows += 1
        n = np.array([float(r[k]) for k in observed_keys])
        lp = np.array([float(r[k]) for k in log_keys])
        assert n.sum() > 0 and np.all(n >= 0) and np.isfinite(lp).all()
        assert abs(np.exp(lp).sum()-1) < 1e-10
        if r['model'] in ('retention_bounded','retention_nonnegative'):
            error = abs(lp[3]-lp[1]+float(r['d']))
            max_odds_error = max(max_odds_error, error); checked_odds += 1
            assert error < 1e-11
        interaction = 'agreeing' if roots[r['root']]['last_two'] in ('BB','FF') else 'opposed'
        key = tuple(r[k] for k in ('analysis_variant','information_protocol','approximation','model','regularization_view'))
        for subset in ('all', interaction):
            groups[key+(subset,)][r['root']].append((n,lp))
    assert rows == verified['rows'] and len(groups) == 144
    summaries = []; conditional = defaultdict(dict)
    labels = ('unraised_old','unraised_opposite','raised_old','raised_opposite','raising','old_harmony')
    for key, rootrows in sorted(groups.items()):
        bins = np.zeros((6,10,3)); cond = {s:{} for s in ('old','opposite')}
        root_metrics=[]; incidences=0
        for root, cells in sorted(rootrows.items()):
            total = sum(n.sum() for n,lp in cells); incidences += total
            metrics = np.zeros(6)
            for n,lp in cells:
                p = np.exp(lp); mass=n.sum(); y=n/mass; weight=mass/total
                pred=np.r_[p,p[2]+p[3],p[0]+p[2]]
                obs=np.r_[y,y[2]+y[3],y[0]+y[2]]
                indices=np.minimum((pred*10).astype(int),9)
                for j,b in enumerate(indices):
                    bins[j,b] += weight*np.array([1.,pred[j],obs[j]])
                metrics += weight*(obs-pred)
            root_metrics.append(metrics)
            for name, (u,v) in {'old':(0,2),'opposite':(1,3)}.items():
                mass=sum(n[u]+n[v] for n,lp in cells)
                if not mass: continue
                observed=predicted=score=brier=0.
                for n,lp in cells:
                    m=n[u]+n[v]
                    if not m: continue
                    logz=np.logaddexp(lp[u],lp[v]); lq=lp[v]-logz; lnq=lp[u]-logz
                    q=np.exp(lq)
                    observed += n[v]; predicted += m*q
                    score += n[v]*lq+n[u]*lnq
                    brier += n[v]*(1-q)**2+n[u]*q**2
                cond[name][root]={'mass':float(mass),'raised':float(observed),'expected_raised':float(predicted),
                    'observed':observed/mass,'predicted':predicted/mass,'residual':(observed-predicted)/mass,
                    'log_score':score/mass,'brier':brier/mass}
        row=dict(zip(('analysis_variant','information_protocol','approximation','model','regularization_view','subset'),key))
        row.update(roots=len(rootrows),incidences=int(incidences),
            root_balanced_observed_minus_predicted=dict(zip(labels,np.mean(root_metrics,axis=0).tolist())),
            calibration_bins={label:[{'lower':b/10,'upper':(b+1)/10,'root_weight_mass':float(v[0]),
                'mean_prediction':float(v[1]/v[0]) if v[0] else None,
                'mean_observed':float(v[2]/v[0]) if v[0] else None} for b,v in enumerate(bins[j])] for j,label in enumerate(labels)})
        summaries.append(row)
        for name,data in cond.items():
            base=(key[0],key[1],key[4],key[5],name)
            conditional[base][(key[2],key[3])] = data
    results=[]
    for base, models in sorted(conditional.items()):
        modelkeys=sorted(models); names=sorted(models[modelkeys[0]])
        assert all(sorted(models[k])==names for k in modelkeys)
        if not names: continue
        x=np.array([[models[k][root]['residual'] for k in modelkeys] for root in names])
        rng=np.random.default_rng(2026092007); boot=np.empty((5000,len(modelkeys)))
        for lo in range(0,5000,250):
            ix=rng.integers(0,len(names),size=(min(250,5000-lo),len(names)))
            boot[lo:lo+len(ix)]=x[ix].mean(axis=1)
        for j,k in enumerate(modelkeys):
            d=models[k]; mass=sum(v['mass'] for v in d.values()); raised=sum(v['raised'] for v in d.values())
            row=dict(zip(('analysis_variant','information_protocol','regularization_view','subset','condition_suffix'),base))
            row.update(approximation=k[0],model=k[1],roots=len(names),conditioned_incidences=int(mass),raised=int(raised),
                root_balanced_observed=float(np.mean([v['observed'] for v in d.values()])),
                root_balanced_predicted=float(np.mean([v['predicted'] for v in d.values()])),
                root_balanced_calibration_residual=float(x[:,j].mean()),
                conditional_root_percentile_95_interval=np.quantile(boot[:,j],[.025,.975],method='linear').tolist(),
                incidence_weighted_observed=raised/mass,
                incidence_weighted_predicted=sum(v['expected_raised'] for v in d.values())/mass,
                root_balanced_conditional_log_score=float(np.mean([v['log_score'] for v in d.values()])),
                root_balanced_conditional_brier=float(np.mean([v['brier'] for v in d.values()])))
            results.append(row)
    out={'utc':datetime.now(timezone.utc).isoformat(),'status':'RETROSPECTIVE_FIXED_PREDICTION_CALIBRATION_COMPUTED',
        'predictions_sha256':digest(a.predictions),'root_table_sha256':digest(a.root_table),'script_sha256':digest(Path(__file__)),
        'rows':rows,'native_opposite_odds_checks':checked_odds,'max_native_opposite_odds_error':max_odds_error,
        'groups':summaries,'conditional_raising':results,'bootstrap_replicates':5000,'seed':2026092007,
        'scope':'Post-ranking diagnostic, no new fits. Conditional ratios exclude only roots with zero observed conditioning mass. Bootstrap holds fits, partitions and observed conditioning cells fixed; not article/speaker independence or selection-adjusted confirmation. Fixed bins describe calibration, not new evaluation selection.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'rows':rows,'groups':len(summaries),'conditional_groups':len(results),'max_odds_error':max_odds_error}))

if __name__=='__main__':main()
