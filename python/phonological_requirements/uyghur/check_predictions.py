from pathlib import Path
from collections import defaultdict
from datetime import datetime,timezone
import argparse,csv,hashlib,json,math
import numpy as np

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
DATA=REPO/'data/uyghur'
ORDER=('unraised_old','unraised_opposite','raised_old','raised_opposite')
GROUP=('analysis_variant','information_protocol','approximation','model','regularization_view')
MODELS={'retention_bounded','retention_nonnegative','current_only','input_plus_surface','HU_plus_surface','retention_bounded_plus_HU'}

def read_csv(path):
    with path.open(newline='',encoding='utf-8') as f:return list(csv.DictReader(f))
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def logsum(xs):
    m=max(xs)
    return m+math.log(sum(math.exp(x-m) for x in xs))

def independent_energies(model,theta,d,q,old_back,opposed):
    previous_back=not old_back if opposed else old_back
    result=[]
    for raised,suffix_back in [(False,old_back),(False,not old_back),(True,old_back),(True,not old_back)]:
        current_back=previous_back if raised else old_back
        cost=d*raised
        if model.startswith('retention_'):
            for direction_back in (False,True):
                initial=old_back==direction_back
                present=current_back==direction_back
                violates=suffix_back!=direction_back
                cost+=theta['A']*initial*violates+theta['B']*(not initial)*present*violates
        elif model=='current_only':cost+=theta['C']*(suffix_back!=current_back)
        elif model=='input_plus_surface':cost+=theta['input']*(suffix_back!=old_back)+theta['surface']*(suffix_back!=current_back)
        elif model=='HU_plus_surface':cost+=theta['surface']*(suffix_back!=current_back)
        else:raise ValueError(model)
        if model in {'HU_plus_surface','retention_bounded_plus_HU'}:
            cost+=theta['HU']*((1-q) if suffix_back else q)
        result.append(cost)
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('predictions',type=Path)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args();args.output_dir.mkdir(exist_ok=False,parents=True)
    panel_path=DATA/'clean_morphology_panel_v3.csv'
    outer_path=DATA/'uyghur_outer_fold_manifest_v1.csv'
    assert digest(panel_path)=='d3ee14c623af2e0c6f7f842d68adfcadc188d05bde8d664b34da020d4964b130'
    assert digest(outer_path)=='fded6710f48c1b63cfec4e8939537836c2a15b43c72b75d789d0a57b7ba448a6'
    roots={r['root']:r for r in read_csv(outer_path)}
    expected=defaultdict(lambda:[0]*4)
    for row in read_csv(panel_path):
        r=row['root']
        if r not in roots or row['morphology'] not in {'dat','loc'} or row['primary_observer_covered'].lower()!='true':continue
        old_back=roots[r]['template'][-1]=='B'
        raised=row['observed_root_surface_class']=='neutral_i'
        opposite=(row['harmony_visibility']=='back')!=old_back
        expected[r,row['morphology'],row['source']][2*raised+opposite]+=int(row['incidences'])
    rows=read_csv(args.predictions)
    assert rows, 'empty prediction export'
    views={r['regularization_view'] for r in rows}
    assert len(views)==1 and views <= {'selected','alpha_zero_numeric_candidate_pending_separability'}
    seen=defaultdict(set);scores=defaultdict(lambda:defaultdict(lambda:np.zeros(4)))
    breakdown=defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:np.zeros(4))))
    max_log_error=0.;factor_errors=[];parameter_folds={}
    for row in rows:
        group=tuple(row[k] for k in GROUP);model=row['model'];root=row['root']
        assert model in MODELS
        info=roots[root];cell=root,row['morphology'],row['source']
        assert int(row['outer_fold'])==int(info['outer_fold'])
        assert cell not in seen[group];seen[group].add(cell)
        counts=np.array([int(row['observed_'+label]) for label in ORDER])
        assert counts.tolist()==expected[cell]
        theta=json.loads(row['parameters_json']);d=float(row['d']);q=float(row['q_HU'])
        assert all(math.isfinite(v) and v>=-1e-10 for v in theta.values())
        if model.startswith('retention_bounded'):assert theta['B']<=theta['A']+1e-10
        if 'HU' in theta:assert math.isfinite(q) and 0<=q<=1
        opposed=info['template'] in {'BF','FB'};old_back=info['template'][-1]=='B'
        energies=independent_energies(model,theta,d,q,old_back,opposed)
        z=logsum([-e for e in energies]);lp=np.array([-e-z for e in energies])
        predicted=np.array([float(row['predicted_'+label]) for label in ORDER])
        assert np.max(abs(np.exp(lp)-predicted))<1e-10
        assert abs(float(sum(predicted))-1)<1e-10
        if all('log_predicted_'+label in row for label in ORDER):
            reported=np.array([float(row['log_predicted_'+label]) for label in ORDER])
            err=float(np.max(abs(lp-reported)));assert err<1e-9;max_log_error=max(max_log_error,err)
        else:
            positive=predicted>0
            assert np.max(abs(np.log(predicted[positive])-lp[positive]))<1e-8
        mass=float(sum(counts))
        raising_lps=np.array([logsum(lp[:2]),logsum(lp[2:])])
        harmony_lps=np.array([logsum(lp[[0,2]]),logsum(lp[[1,3]])])
        contribution=np.array([float(counts@lp),float(np.array([sum(counts[:2]),sum(counts[2:])])@raising_lps),float(np.array([counts[0]+counts[2],counts[1]+counts[3]])@harmony_lps),mass])
        scores[group][root]+=contribution
        categories={'interaction':'opposed' if opposed else 'agreeing','morphology':row['morphology'],'source':row['source'],'template':info['template'],'final_vowel':info['final_low_vowel'],'acc_interpretable':info['acc_interpretable_available'],'acc_input':info['acc_input_available']}
        for category,label in categories.items():breakdown[group][category+'='+str(label)][root]+=contribution
        if model in {'retention_bounded','retention_nonnegative','current_only'}:
            shift=raising_lps[1]-raising_lps[0]+d
            theory=(logsum([-theta['B'],-theta['A']])-logsum([0.,-theta['A']])) if opposed and model.startswith('retention') else 0.
            factor_errors.append(abs(shift-theory))
            assert abs(shift-theory)<1e-9
        pkey=group+(row['outer_fold'],)
        fields={k:row[k] for k in ('fit_alpha','selected_alpha','parameters_json','native_coordinates_json','training_block_hash','grammar_fit_hash')}
        assert pkey not in parameter_folds or parameter_folds[pkey]==fields
        parameter_folds[pkey]=fields
    expected_groups=set()
    for variant in ('all_strict','all_agreeing_offsets','unrounded_strict'):
        for protocol in ('side_informed','wholly_unseen'):
            for model in MODELS:
                approximations=('laplace','gh80') if model in {'HU_plus_surface','retention_bounded_plus_HU'} else ('not_applicable',)
                for approximation in approximations:
                    expected_groups.add((variant,protocol,approximation,model,next(iter(views))))
    assert set(seen)==expected_groups, 'incomplete prespecified comparison export'
    for group,members in seen.items():
        admissible={cell for cell in expected if group[0]!='unrounded_strict' or roots[cell[0]]['unrounded'].lower()=='true'}
        assert members==admissible,(group,len(members),len(admissible))
    def summarize(s):
        matrix=np.array(list(s.values()))
        return {'roots':len(s),'incidences':int(matrix[:,3].sum()),'root_balanced_joint':float(np.mean(matrix[:,0]/matrix[:,3])),
            'incidence_weighted_joint':float(matrix[:,0].sum()/matrix[:,3].sum()),
            'root_balanced_raising':float(np.mean(matrix[:,1]/matrix[:,3])),
            'root_balanced_harmony_old_vs_opposite':float(np.mean(matrix[:,2]/matrix[:,3]))}
    summaries=[];per_root=[]
    for group,s in sorted(scores.items()):
        common=dict(zip(GROUP,group))
        summaries.append({**common,**summarize(s),'breakdowns':{k:summarize(v) for k,v in sorted(breakdown[group].items())}})
        for root,v in sorted(s.items()):per_root.append({**common,'root':root,'incidences':int(v[3]),'joint':float(v[0]/v[3]),'raising':float(v[1]/v[3]),'harmony':float(v[2]/v[3])})
    (args.output_dir/'group_summaries.json').write_text(json.dumps(summaries,indent=2)+'\n')
    (args.output_dir/'per_root_scores.json').write_text(json.dumps(per_root,indent=2)+'\n')
    (args.output_dir/'fold_parameters.json').write_text(json.dumps([dict(zip(GROUP+('outer_fold',),k),**v) for k,v in sorted(parameter_folds.items())],indent=2)+'\n')
    report={'utc':datetime.now(timezone.utc).isoformat(),'status':'INDEPENDENT_OOF_SEMANTICS_COUNTS_SCORES_PASS',
        'predictions_sha256':digest(args.predictions),'script_sha256':digest(Path(__file__)),
        'rows':len(rows),'groups':len(scores),'max_log_probability_error':max_log_error,
        'max_retention_or_current_raising_factor_error':max(factor_errors,default=0.),
        'scope':'Independent primitive scorer and exact source-cell matching; complete OOF row coverage and score/marginal recomputation. Conditional on supplied verified fits. Does not certify calibration, causality, iid sampling, mathematical MLE existence, or publication readiness.'}
    (args.output_dir/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))

if __name__=='__main__':main()
