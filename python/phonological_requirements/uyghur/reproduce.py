                                                                                 

                                                                          
                                                                            
                                                                        
   
from pathlib import Path
import argparse, csv, hashlib, json, subprocess, sys

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
SETTINGS=('uniform20','uniform50','half20','half50')
FIELDS=('analysis_variant','information_protocol','approximation','model','regularization_view',
        'roots','incidences','root_balanced_joint','incidence_weighted_joint',
        'root_balanced_raising','root_balanced_harmony_old_vs_opposite')

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description='Independently rescore the released Uyghur fits and reproduce every comparison.\n\nThis is a replay of fitted predictions, not a rerun of the optimizers. Use\nexperiment.py --fit for new fitting. Likelihood inspection is available with\n--likelihood-checks and preserves the measured quadrature discrepancies.\n')
    ap.add_argument('--output-dir',type=Path,default=REPO/'build/uyghur/replay')
    ap.add_argument('--likelihood-checks',action='store_true')
    a=ap.parse_args();a.output_dir.mkdir(parents=True,exist_ok=False)
    released=REPO/'results/uyghur'
    manifest=json.loads((released/'fit_manifest.json').read_text())
    for setting in SETTINGS:
        base=released/'fits'/setting
        for relative,expected in manifest['settings'][setting]['files'].items():
            assert sha(base/relative)==expected,(setting,relative)
    commands=[]
    def run(script,*argv):
        cmd=[sys.executable,str(HERE/script),*map(str,argv)]
        log=a.output_dir/f'command_{len(commands)+1:03d}.log'
        with log.open('w') as out:
            p=subprocess.run(cmd,cwd=REPO,stdout=out,stderr=subprocess.STDOUT)
        commands.append({'script':script,'exit_code':p.returncode,'log':log.name,'log_sha256':sha(log)})
        if p.returncode:
            print(log.read_text(errors='replace')[-3000:])
            raise RuntimeError(f'{script} failed: {p.returncode}')
    run('experiment.py','--validate-only')
    run('check_partitions.py')
    run('check_algebra.py')
    scores=[];contrasts=[]
    for setting in SETTINGS:
        base=released/'fits'/setting
        for view in ('selected','alpha0'):
            pred=base/f'uyghur_oof_predictions_{view}_v1.csv'
            dest=a.output_dir/f'{setting}_{view}'
            run('check_predictions.py',pred,'--output-dir',dest)
            run('check_information.py',pred,'--output',dest/'information.json')
            run('calibration.py',pred,'--root-table',REPO/'data/uyghur/clean_transfer_root_table_v2.csv',
                '--verified-result',dest/'result.json','--output',dest/'calibration.json')
            for row in json.loads((dest/'group_summaries.json').read_text()):
                scores.append({'setting':setting,**{k:row[k] for k in FIELDS}})
            for metric in ('joint','raising','harmony'):
                out=dest/f'bootstrap_{metric}.json'
                run('paired_bootstrap.py',dest/'per_root_scores.json','--output',out,'--metric',metric)
                result=json.loads(out.read_text());assert len(result['comparisons'])==180
                for original in result['comparisons']:
                    row=dict(original);lo,hi=row.pop('conditional_paired_root_percentile_95_interval')
                    contrasts.append({'setting':setting,'metric':metric,**row,
                                      'conditional_95_lower':lo,'conditional_95_upper':hi})
            print(setting,view,'checked',flush=True)
        if a.likelihood_checks:
            run('check_hu_fits.py',base,'--output-dir',a.output_dir/f'{setting}_likelihood')
            print(setting,'likelihood checked',flush=True)
    assert len(scores)==384 and len(contrasts)==4320
    matches={}
    for name,rows in (('all_model_scores.tsv',scores),('all_paired_contrasts.tsv',contrasts)):
        p=a.output_dir/name
        with p.open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter='\t')
            writer.writeheader();writer.writerows(rows)
        with (released/name).open(newline='') as f:expected=list(csv.DictReader(f,delimiter='\t'))
        with p.open(newline='') as f:actual=list(csv.DictReader(f,delimiter='\t'))
        assert expected==actual,f'Recomputed table differs: {name}'
        matches[name]={'rows':len(rows),'sha256':sha(p),'released_table_equal':True}
    report={'status':'INDEPENDENT_RELEASED_PREDICTION_REPLAY_PASS','tables':matches,
            'commands':commands,'likelihood_checks':a.likelihood_checks,
            'scope':'All prespecified settings and contrasts, with fixed fitted values, folds and nuisance estimates. Paired-root uncertainty does not include refitting or establish speaker/article independence. This does not assert predictive superiority of retention.'}
    (a.output_dir/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='commands'},indent=2))

if __name__=='__main__':main()
