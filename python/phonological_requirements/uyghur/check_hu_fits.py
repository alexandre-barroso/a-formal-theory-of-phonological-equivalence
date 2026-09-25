from pathlib import Path
from collections import defaultdict
import argparse,csv,hashlib,json,math,sys
import numpy as np
from scipy.special import gammaln,logsumexp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
DATA=REPO/'data/uyghur'
import uyghur_laplace_vectorized_v3 as laplace
import uyghur_gh_vectorized_v3 as gh
import uyghur_hu_scalar_reference_v1 as scalar_reference

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read_json(p):return json.loads(p.read_text())
def count(row,key):
    v=float(row[key]);assert v>=0 and v.is_integer();return int(v)

def reconstruct(cache_dir,record,table):
    baseline=read_json(cache_dir/('beta_'+record['beta_key']+'.json'))
    roots=baseline['roots'];assert len(roots)==len(set(roots))
    acc={r:(count(table[r],'acc_neutral_i_e'),count(table[r],'acc_neutral_i_e')+count(table[r],'acc_unraised')) for r in roots}
    freq=np.array([math.log1p(acc[r][1]) for r in roots]);mean=float(freq.mean());sd=float(freq.std())
    assert abs(mean-record['log_frequency_mean'])<1e-12 and abs(sd-record['log_frequency_sd'])<1e-12
    ids=[];design=[];success=[];total=[]
    for r in roots:
        row=table[r];y=sum(count(row,f'{m}_primary_{z}_back') for m in ('dat','loc') for z in ('raised','unraised'))
        n=y+sum(count(row,f'{m}_primary_{z}_front') for m in ('dat','loc') for z in ('raised','unraised'))
        if not n:continue
        prior=baseline['fits'][row['final_low_vowel']];a=prior['alpha'];b=prior['beta'];k,nt=acc[r]
        rho=(k+a)/(nt+a+b);f=float(row['last_two'][-1]=='F');l=(math.log1p(nt)-mean)/sd
        name=r.endswith('name');ane=r.endswith('ane') and r not in {'bahane','epsane',"i'ane",'jerimane','perwane','perghane','péshane','zamane'}
        che=r.endswith('che') and r not in {'anche','bunche','qanche','birqanche'}
        design.append([1,f,l,rho,f*l,f*rho,l*rho,f*l*rho,float(name),float(ane),float(che)])
        ids.append(r);success.append(y);total.append(n)
    return np.array(design),np.array(success),np.array(total),ids

def root_loglaws(theta,X,y,n,order):
    eta=X@theta[:-1];sigma=math.exp(theta[-1]);b,u,c,_,_=laplace.mode_state(eta,y,n,sigma)
    nodes,logweights=gh.nodes_weights(order);scale=np.sqrt(2/c)
    shift=b[:,None]+scale[:,None]*nodes;totaleta=u[:,None]+scale[:,None]*nodes
    value=-y[:,None]*np.logaddexp(0,-totaleta)-(n-y)[:,None]*np.logaddexp(0,totaleta)-shift**2/(2*sigma**2)-math.log(sigma*math.sqrt(2*math.pi))
    constants=gammaln(n+1)-gammaln(y+1)-gammaln(n-y+1)
    return constants+np.log(scale)+logsumexp(logweights+value+nodes**2,axis=1)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('run',type=Path);parser.add_argument('--output-dir',type=Path,required=True);args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=False)
    tablepath=DATA/'clean_transfer_root_table_v2.csv';assert sha(tablepath)=='8ed463dba3e78218a1625bc073c58562ff4c07d1bbc83ce06e52c4a12e31ecb0'
    with tablepath.open(newline='') as f:table={r['root']:r for r in csv.DictReader(f)}
    cache=args.run/'fit_cache';paths=sorted(cache.glob('hu_*.json'));assert paths
    results=[]
    for path in paths:
        record=read_json(path);fit=record['fit'];X,y,n,ids=reconstruct(cache,record,table)
        beta=np.array(fit['beta']);sigma=fit['sigma'];theta=np.r_[beta,math.log(sigma)];tau=fit['tau']
        assert X.shape==(len(ids),11) and beta.shape==(11,) and tau in (20.,50.)
        assert fit['converged'] and fit['design_rank']==np.linalg.matrix_rank(X)
        penalty=float(sum(float(b)**2 for b in beta)/(2*tau**2))
        scalar=scalar_reference.negative_log_likelihood(beta,sigma,X,y,n,record['approximation'])
        objective_error=abs(scalar+penalty-fit['objective']);assert objective_error<1e-6
        laws={order:root_loglaws(theta,X,y,n,order) for order in (40,80,160,320)}
        assert abs(float(laws[80].sum())+gh.objective(theta,X,y,n,80))<1e-7
        changes={f'{a}_{b}':float(np.max(abs(laws[a]-laws[b]))) for a,b in ((40,80),(80,160),(160,320))}
        
        selected=set(np.argsort(abs(laws[80]-laws[320]))[-3:].tolist())
        selected.update((int(np.argmax(n)),int(np.argmin(n)),int(np.argmax(abs(X@beta)))))
        direct=[]
        for i in sorted(selected):
            reference=scalar_reference.root_loglik_quad(beta,sigma,X[i:i+1],y[i:i+1],n[i:i+1])
            direct.append({'root':ids[i],'n':int(n[i]),'y':int(y[i]),'eta':float(X[i]@beta),'reference':reference,'errors':{str(order):float(abs(law[i]-reference)) for order,law in laws.items()}})
        
        results.append({'cache':str(path.relative_to(args.run)),'cache_sha256':sha(path),'approximation':record['approximation'],'tau':tau,'rows':len(ids),'rank':int(np.linalg.matrix_rank(X)),'penalty':penalty,'independent_scalar_objective_error':objective_error,'root_loglik_refinement_max':changes,'summed_loglik_by_order':{str(order):float(v.sum()) for order,v in laws.items()},'direct_inspections':direct})
        (args.output_dir/'checks.jsonl').open('a').write(json.dumps(results[-1])+'\n')
    report={'status':'CACHE_RECONSTRUCTION_OBJECTIVE_CHECKS_COMPLETE_QUADRATURE_DISCREPANCIES_FOR_REVIEW','script_sha256':sha(Path(__file__)),'fits':len(results),'max_objective_error':max(r['independent_scalar_objective_error'] for r in results),'max_80_320_root_difference':max(r['root_loglik_refinement_max']['80_160']+r['root_loglik_refinement_max']['160_320'] for r in results),'scope':'Independent root-table counts, full native design and source scalar likelihood reconstruction. Actual fitted quadrature refinement and selected direct integrals; no global optimizer, empirical adequacy or full OOF completion certification.'}
    (args.output_dir/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))

if __name__=='__main__':main()
