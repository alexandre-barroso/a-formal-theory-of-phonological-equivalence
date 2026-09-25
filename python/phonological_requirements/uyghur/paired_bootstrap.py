from pathlib import Path
from datetime import datetime,timezone
from itertools import combinations
import argparse,hashlib,json
import numpy as np

MODELS=('retention_bounded','retention_nonnegative','current_only','input_plus_surface','HU_plus_surface','retention_bounded_plus_HU')
HU={'HU_plus_surface','retention_bounded_plus_HU'}

def main():
    p=argparse.ArgumentParser();p.add_argument('per_root_scores',type=Path);p.add_argument('--output',type=Path,required=True);p.add_argument('--metric',choices=('joint','raising','harmony'),required=True);a=p.parse_args()
    data=json.loads(a.per_root_scores.read_text())
    table={}
    for row in data:
        key=tuple(row[k] for k in ('analysis_variant','information_protocol','approximation','model','regularization_view'))
        table.setdefault(key,{})[row['root']]=row
    results=[]
    views=sorted({r['regularization_view'] for r in data});assert len(views)==1
    for variant in ('all_strict','all_agreeing_offsets','unrounded_strict'):
        for protocol in ('side_informed','wholly_unseen'):
            for approximation in ('laplace','gh80'):
                columns=[table[variant,protocol,approximation if model in HU else 'not_applicable',model,views[0]] for model in MODELS]
                roots=sorted(columns[0]);assert roots and all(set(c)==set(roots) for c in columns)
                x=np.array([[c[root][a.metric] for c in columns] for root in roots])
                rng=np.random.default_rng(2026092007)
                boot=np.empty((5000,len(MODELS)))
                for lo in range(0,5000,250):
                    indices=rng.integers(0,len(roots),size=(min(250,5000-lo),len(roots)))
                    boot[lo:lo+len(indices)]=x[indices].mean(axis=1)
                for i,j in combinations(range(len(MODELS)),2):
                    delta=x[:,i]-x[:,j];replicate=boot[:,i]-boot[:,j]
                    interval=np.quantile(replicate,[.025,.975],method='linear')
                    results.append({'analysis_variant':variant,'information_protocol':protocol,'approximation':approximation,'regularization_view':views[0],
                        'model_a':MODELS[i],'model_b':MODELS[j],'roots':len(roots),'mean_log_score_a_minus_b':float(delta.mean()),
                        'conditional_paired_root_percentile_95_interval':interval.tolist(),
                        'root_wins_a':int((delta>0).sum()),'root_ties':int((delta==0).sum()),'replicates':5000,'seed':2026092007})
    assert len(results)==180
    out={'utc':datetime.now(timezone.utc).isoformat(),'status':'PAIRED_ROOT_BOOTSTRAP_COMPUTED_CONDITIONAL_ON_FIXED_FITS',
        'source_sha256':hashlib.sha256(a.per_root_scores.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'resampling':'Uniform with replacement over sorted root spellings; identical seed and paired root samples for every matched model column. Intervals use the linear 2.5%/97.5% quantiles.',
        'metric':a.metric,
        'scope':'Fixed folds, nuisance estimates, model selection and fitted grammars; does not include their refitting uncertainty or establish independence of source incidences, articles, roots, or speakers. Full table, no multiplicity-adjusted confirmatory significance claim.',
        'comparisons':results}
    assert not a.output.exists();a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'metric':a.metric,'comparisons':len(results),'output':str(a.output)}))

if __name__=='__main__':main()
