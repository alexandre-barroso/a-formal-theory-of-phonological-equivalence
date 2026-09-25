from pathlib import Path
import argparse,csv,hashlib,json,math
from functools import lru_cache
import numpy as np
from scipy.special import expit

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
DATA=REPO/'data/uyghur'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def csvrows(p):
    with p.open(newline='') as f:return list(csv.DictReader(f))
def count(row,k):
    value=float(row[k]);assert value.is_integer() and value>=0;return int(value)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('predictions',type=Path);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    tablepath=DATA/'clean_transfer_root_table_v2.csv';outerpath=DATA/'uyghur_outer_fold_manifest_v1.csv'
    assert sha(tablepath)=='8ed463dba3e78218a1625bc073c58562ff4c07d1bbc83ce06e52c4a12e31ecb0'
    assert sha(outerpath)=='fded6710f48c1b63cfec4e8939537836c2a15b43c72b75d789d0a57b7ba448a6'
    table={r['root']:r for r in csvrows(tablepath)};outer={r['root']:r for r in csvrows(outerpath)}
    rows=csvrows(args.predictions);assert rows
    cache=args.predictions.parent/'fit_cache'
    @lru_cache(None)
    def get(kind,key):
        record=json.loads((cache/(kind+'_'+key+'.json')).read_text());assert record['cache_key']==key;return record
    rho_priors={r['rho_prior'] for r in rows};taus={float(r['hu_tau']) for r in rows};estimators={r['hu_estimator'] for r in rows}
    assert len(rho_priors)==len(taus)==len(estimators)==1
    assert rho_priors<={'uniform','beta_half_half'} and taus<={20.,50.}
    max_d_error=0.;max_q_error=0.;hu_rows=0;seen_fits=set();checked_blocks=set()
    for row in rows:
        root=row['root'];record=table[root];grammar=get('grammar',row['grammar_fit_hash']);seen_fits.add(grammar['cache_key'])
        assert grammar['model']==row['model'] and grammar['variant']==row['analysis_variant']
        assert grammar['block_key']==row['training_block_hash'] and grammar['alpha']==float(row['fit_alpha'])
        assert grammar['gate']['passed'] and grammar['fit']['converged']
        assert grammar['fit']['parameters']==json.loads(row['parameters_json'])
        baseline=get('beta',grammar['beta_key']);assert baseline['rho_prior']==row['rho_prior']
        assert baseline['block_key']==grammar['block_key'] and root not in baseline['roots']
        block_id=(grammar['block_key'],int(row['outer_fold']),row['analysis_variant'])
        if block_id not in checked_blocks:
            expected={r for r,v in outer.items() if int(v['outer_fold'])!=int(row['outer_fold']) and (row['analysis_variant']!='unrounded_strict' or v['unrounded'].lower()=='true')}
            assert set(baseline['roots'])==expected;checked_blocks.add(block_id)
        a=baseline['fits'][record['final_low_vowel']]['alpha'];b=baseline['fits'][record['final_low_vowel']]['beta']
        visible=row['information_protocol']=='side_informed';assert row['information_protocol'] in {'side_informed','wholly_unseen'}
        k=count(record,'acc_neutral_i_e') if visible else 0;n=k+count(record,'acc_unraised') if visible else 0
        rho=(k+a)/(n+a+b);d=math.log((1-rho)/rho)
        if grammar['offset_key'] is not None:
            offset=get('offset',grammar['offset_key']);assert offset['beta_key']==grammar['beta_key']
            assert row['analysis_variant']=='all_agreeing_offsets';d+=offset[row['morphology']]
        else:assert row['analysis_variant']!='all_agreeing_offsets'
        d_error=abs(d-float(row['d']));assert d_error<1e-10;max_d_error=max(max_d_error,d_error)
        if grammar['hu_key'] is not None:
            hu=get('hu',grammar['hu_key']);assert hu['beta_key']==grammar['beta_key'] and hu['block_key']==grammar['block_key']
            assert hu['fit']['tau']==float(row['hu_tau']) and hu['fit']['converged']
            f=float(record['last_two'][-1]=='F');l=(math.log1p(n)-hu['log_frequency_mean'])/hu['log_frequency_sd']
            name=root.endswith('name');ane=root.endswith('ane') and root not in {'bahane','epsane',"i'ane",'jerimane','perwane','perghane','péshane','zamane'}
            che=root.endswith('che') and root not in {'anche','bunche','qanche','birqanche'}
            X=np.array([1,f,l,rho,f*l,f*rho,l*rho,f*l*rho,float(name),float(ane),float(che)])
            q=float(expit(X@np.asarray(hu['fit']['beta'])));error=abs(q-float(row['q_HU']));assert error<1e-12
            max_q_error=max(max_q_error,error);hu_rows+=1
        else:assert math.isnan(float(row['q_HU']))
    result={'status':'PASS_OOF_NUISANCE_INFORMATION_AND_CACHE_CORRESPONDENCE','script_sha256':sha(Path(__file__)),'prediction_sha256':sha(args.predictions),'rows':len(rows),'hu_rows':hu_rows,'grammar_fits':len(seen_fits),'training_blocks':len(checked_blocks),'rho_prior':next(iter(rho_priors)),'hu_tau':next(iter(taus)),'hu_estimator':next(iter(estimators)),'max_d_error':max_d_error,'max_q_error':max_q_error,'scope':'All exported d and q reconstructed from independent counts and actual training caches, with outer-root separation and fixed-effects-only HU evaluation. Does not independently refit the nuisance models.'}
    assert not args.output.exists();args.output.parent.mkdir(exist_ok=True,parents=True);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
