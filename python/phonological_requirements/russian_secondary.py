from pathlib import Path
from collections import Counter, defaultdict
import argparse
import csv
import hashlib
import json
import numpy as np
from scipy.special import expit, logsumexp
from .certificate import read, write
from .russian_design import RussianDesign, read_responses, dictionary_tokens, fold


def checked_inputs(directory):
    manifest=read('russian_inputs.json')
    files={n:directory/n for n in manifest['files']}
    for n,p in files.items():
        if hashlib.sha256(p.read_bytes()).hexdigest()!=manifest['files'][n]['sha256']:raise ValueError('Input hash mismatch: '+n)
    return files


def prepare(directory, work):
    files=checked_inputs(directory)
    design=RussianDesign(files['feature_chart_given_to_learners.txt'],files['sublexical_learner_predictions_with_faithfulness.txt'])
    raw,rows=read_responses(files['experiment_results.txt'])
    with files['train.txt'].open() as f:training=list(csv.reader(f,delimiter='\t'))
    lexical=[r for r in training if tuple(r[1].split()[-3:]) not in [('o','g','o'),('e','g','o')]]
    with files['lexicon_2nd_declension_masculines.txt'].open() as f:dictionary=list(csv.DictReader(f,delimiter='\t'))
    full_bases={dictionary_tokens(r['nomsgT']) for r in dictionary}
    overlapping=sorted({r['model_base'] for r in rows}&full_bases)
    source_pairs=defaultdict(list)
    for i,r in enumerate(dictionary,2):source_pairs[(dictionary_tokens(r['nomsgT']),dictionary_tokens(r['gensgT']))].append((i,r))
    if Counter(map(tuple,training[:1902])) != Counter((dictionary_tokens(r['nomsgT']),dictionary_tokens(r['gensgT'])) for r in dictionary if r['yer']=='TRUE'):raise ValueError('Training yer stratum identity changed')
    if not all(any(r['yer']=='FALSE' for _,r in source_pairs[tuple(pair)]) for pair in training[1902:]):raise ValueError('Training non-yer stratum unmatched')
    source_mismatch=[]
    for i,(base,target) in enumerate(training,1):
        if [base,target] not in lexical:continue
        ref,ys,j,k=design.generate(tuple(base.split()))
        y=next(y for y in ys if ' '.join(t for t in y if t!='∅')==target)
        if i>1902 and y[j]=='∅' and any(r['yer']=='FALSE' for _,r in source_pairs[(base,target)]):
            source_mismatch.append({'training_line':i,'source_rows':[line for line,r in source_pairs[(base,target)] if r['yer']=='FALSE']})
    arrays=[];metas=[];starts=[];lengths=[];ranges=[];shift=0
    for bases in [[r[0] for r in lexical],[r['model_base'] for r in rows]]:
        ar,ran,meta=design.coefficients(bases);arrays.append(ar);ranges.append({x:(a+shift,b+shift) for x,(a,b) in ran.items()});starts.extend(a+shift for a,b in ran.values());lengths.extend(b-a for a,b in ran.values());metas.extend(meta);shift+=len(meta)
    data={k:np.vstack([a[k] for a in arrays]) for k in arrays[0]}
    starts=np.asarray(starts);lengths=np.asarray(lengths);groups=np.repeat(np.arange(len(starts)),lengths)
    nlex=len(arrays[0]['current']);nglex=len(ranges[0]);yc=np.zeros(len(metas));gc=np.zeros(len(starts));validation=np.zeros(len(starts),bool)
    for base,(a,b) in ranges[0].items():validation[groups[a]]=fold('rus-lex-v1|',base)==0
    for base,target in lexical:
        a,b=ranges[0][base];fiber=[i for i in range(a,b) if metas[i]['output']==target]
        if len(fiber)!=1:raise ValueError('Lexical fiber not singleton')
        yc[fiber[0]]+=1;gc[groups[fiber[0]]]+=1
    for r in rows:
        a,b=ranges[1][r['model_base']]
        for key,outkey in [('faithful_row','presented_faithful'),('deletion_row','presented_deletion')]:
            fiber=[i for i in range(a,b) if metas[i]['output']==r[outkey]]
            if len(fiber)!=1:raise ValueError('Displayed fiber not singleton')
            r[key]=fiber[0]
    data.update(starts=starts,lengths=lengths,groups=groups,ycounts=yc,groupcounts=gc,lexvalidation=validation,nlex=nlex,nglex=nglex)
    np.savez_compressed(work/'design.npz',**data)
    (work/'response_rows.json').write_text(json.dumps(rows,ensure_ascii=False))
    (work/'metadata.json').write_text(json.dumps({'rows':metas,'ranges':ranges,'overlap':overlapping},ensure_ascii=False))
    out={'raw_trials':len(raw),'target_trials':len(rows),'participants':len({r['userCode'] for r in rows}),'clusters':len({r['cluster'] for r in rows}),'lexical_records':len(lexical),'lexical_bases':nglex,'experimental_bases':len(ranges[1]),'candidates':len(metas),'lexical_validation_bases':int(validation.sum()),'excluded_go':len(training)-len(lexical),'source_stratum_mismatches':source_mismatch,'dictionary_overlap_bases':len(overlapping),'dictionary_overlap_trials':sum(r['model_base'] in overlapping for r in rows),'offset_status':'Conditional deletion-stratum sensitivity; source non-yer membership is not singular nondeletion.','observed_lexical_deletions':int(yc@(data['faithfulness'][:,0]>0)),'new_response_exclusions':0,'duplicate_participant_trial_pairs':len(raw)-len({(r['userCode'],r['trialnumber']) for r in raw})}
    write('russian_preparation.json',out,work)
    print(json.dumps(out),flush=True)


def design_check(data, work):
    if not np.array_equal(data['right_old']+data['right_new'],data['current']):raise ValueError('Current HG coefficient bridge failed')
    rows=json.loads((work/'response_rows.json').read_text());pairs=[];seen=set()
    for r in rows:
        if r['model_base'] in seen:continue
        seen.add(r['model_base']);pairs.append((r['deletion_row'],r['faithful_row']))
    d,f=np.array(pairs).T
    a=np.c_[data['right_old'][d]-data['right_old'][f],data['faithfulness'][d]-data['faithfulness'][f]]
    b=np.c_[data['right_new'][d]-data['right_new'][f],np.zeros((len(d),3),dtype=int)]
    unique,inverse=np.unique(np.c_[a,b],axis=0,return_inverse=True)
    certificate=read('russian_displayed_matrices.json')
    if not np.array_equal(unique[:,:136],certificate['A']) or not np.array_equal(unique[:,136:],certificate['B']) or not np.array_equal(inverse,certificate['row_map']):raise ValueError('Native input/finite Lean table mismatch')
    old=np.any(a!=0,axis=0)
    w=np.r_[np.full(133,.1),[2.,1.,1.]];v=np.where(old,w,w/4)
    ca=np.c_[data['right_old']+data['right_new']/4,data['faithfulness']]@w
    cb=np.c_[data['current'],data['faithfulness']]@v
    if np.max(abs(ca[d]-ca[f]-cb[d]+cb[f]))>1e-12:raise ValueError('Displayed contrast mismatch')
    metadata=json.loads((work/'metadata.json').read_text());start,end=metadata['ranges'][1]['p fj e ch']
    pa=np.exp(-ca[start:end]-logsumexp(-ca[start:end]));pb=np.exp(-cb[start:end]-logsumexp(-cb[start:end]))
    if abs(pa[0]-pb[0])<=.001:raise ValueError('Full law counterexample failed')
    write('russian_design_check.json',{'status':'PASS','integer_cells':2*3698*136,'complete_candidates':len(ca),'current_HG_coefficient_cells':int(data['current'].size),'current_HG_full_support':True,'current_HG_bridge_scope':'Right-old plus right-new equals independently counted current markedness for every declared lexical and experimental candidate; this identity is not asserted for the left-anchor sensitivity.','displayed_contrast_rows':len(a),'pure_old_columns':int(old.sum()),'pure_new_columns':int(np.any(b!=0,axis=0).sum()),'row_map_matches_Lean_certificate':True,'witness_costs_quarter':ca[start:end].tolist(),'witness_costs_current':cb[start:end].tolist(),'witness_probability_quarter':pa.tolist(),'witness_probability_current':pb.tolist(),'witness_scope':'Synthetic actual-design example; equal displayed odds do not entail equal complete-support probabilities.'},work)


def matrix(data, record):
    left=record['sampling'].endswith('_left');o=data['left_old' if left else 'right_old'];n=data['left_new' if left else 'right_new'];f=data['faithfulness'];family=record['family']
    if family=='ordinary':x=np.c_[data['current'],f]
    elif family=='retained':x=np.c_[o+record['lambda']*n,f]
    elif family=='expanded':x=np.c_[o,n,f]
    elif family=='sublexical':
        op=(f[:,0]>0).astype(int)*2+(f[:,1:].sum(axis=1)>0).astype(int)
        x=np.concatenate([data['base_marks']*(op==j)[:,None] for j in range(4)]+[data['current']*(op==j)[:,None] for j in range(4)]+[f,np.eye(4)[op,1:]],axis=1)
    else:raise ValueError(family)
    return x[:,record['keep']].astype(float)


def normalized(cost,starts,lengths):
    return np.concatenate([-cost[a:a+n]-logsumexp(-cost[a:a+n]) for a,n in zip(starts,lengths)])


def lexical_replay(data, parameters, work):
    laws={};checks=[];nlex=int(data['nlex']);nglex=int(data['nglex']);gr=data['groups'][:nlex];yc=data['ycounts'][:nlex];gc=data['groupcounts'][:nglex]
    for record in parameters['lexical']:
        x=matrix(data,record);w=np.array(record['coefficients']);law=normalized(x@w,data['starts'],data['lengths'])
        if record['seed']==0:laws[record['sampling']+'|'+record['model']]=law
        offset=np.where(data['faithfulness'][:nlex,0]>0,0,np.log(600/18661)) if record['sampling'].startswith('corrected') else np.zeros(nlex)
        log_sample=normalized(-law[:nlex]-offset,data['starts'][:nglex],data['lengths'][:nglex])
        obj=float(-yc@log_sample+record['rho']/2*(w@w));gradient=x[:nlex].T@(yc-gc[gr]*np.exp(log_sample))+record['rho']*w
        nn=np.asarray(record['keep'])<1067 if record['family']=='sublexical' else np.ones(len(w),bool)
        gradient[nn&(w<1e-8)&(gradient>0)]=0
        pg=float(max(abs(gradient)));error=abs(obj-record['objective'])
        if pg>1.01e-5 or error>1e-7 or np.min(w[nn])<0:raise ValueError((record['sampling'],record['model'],pg,error))
        checks.append({k:record[k] for k in ['sampling','model','seed']}|{'objective':obj,'objective_error':error,'projected_gradient':pg})
    np.savez_compressed(work/'loglaws.npz',**laws)
    return checks


def crossed_interval(rows,mask,values,resamples):
    rr=[r for r,t in zip(rows,mask) if t];values=values[mask]
    ps=sorted({r['userCode'] for r in rr});cs=sorted({r['cluster'] for r in rr});pm={v:i for i,v in enumerate(ps)};cm={v:i for i,v in enumerate(cs)}
    ind=np.array([pm[r['userCode']]*len(cs)+cm[r['cluster']] for r in rr]);shape=(len(ps),len(cs))
    count=np.bincount(ind,minlength=len(ps)*len(cs)).reshape(shape);total=np.bincount(ind,weights=values,minlength=len(ps)*len(cs)).reshape(shape)
    gen=np.random.default_rng(2026092001);samples=[]
    for _ in range(resamples):
        a=gen.multinomial(len(ps),np.ones(len(ps))/len(ps));b=gen.multinomial(len(cs),np.ones(len(cs))/len(cs));mult=a[:,None]*b[None,:];denom=np.sum(mult*count)
        if denom:samples.append(np.sum(mult*total)/denom)
    return {'difference':float(values.mean()),'interval95':np.quantile(samples,[.025,.975]).tolist(),'resamples':len(samples),'participants':len(ps),'clusters':len(cs)}


def response_replay(data,parameters,work,resamples,variant):
    rows=json.loads((work/'response_rows.json').read_text());metadata=json.loads((work/'metadata.json').read_text())
    if variant=='no_overlap':rows=[r for r in rows if r['model_base'] not in metadata['overlap']]
    y=np.array([[int(r['accept.faithful']),int(r['accept.deletion'])] for r in rows]);ix=np.array([[r['faithful_row'],r['deletion_row']] for r in rows])
    pt=np.array([r['person_test'] for r in rows]);ct=np.array([r['cluster_test'] for r in rows]);splits={'calibration':~pt&~ct,'primary_both':pt&ct,'participant_only':pt&~ct,'cluster_only':~pt&ct};cal=splits['calibration'];discord=y.sum(axis=1)==1
    first=np.array([[r['order']=='TRUE',r['order']!='TRUE'] for r in rows],float);trial=np.array([int(r['trialnumber']) for r in rows],float);trial=(trial-trial[cal].mean())/74
    laws=np.load(work/'loglaws.npz');losses={};out={'variant':variant,'splits':{k:{'trials':int(v.sum()),'participants':len({r['userCode'] for r,t in zip(rows,v) if t}),'clusters':len({r['cluster'] for r,t in zip(rows,v) if t})} for k,v in splits.items()},'fits':[],'contrasts':[]}
    for r in parameters['response']:
        if r['variant']!=variant:continue
        lp=laws[r['sampling']+'|'+r['model']];logs=lp[ix];coef=np.array(r['coefficients']);key=r['sampling']+'|'+r['model']+'|'+r['link'];link=r['link']
        if link=='paired_discordant':
            X=np.c_[logs[:,1]-logs[:,0],first[:,1]-first[:,0]];eta=X@coef;Y=y[:,1];mask=cal&discord;beta=0
        else:
            x=logs.copy()
            if link=='logit_probability':
                for i in range(len(rows)):
                    for j in [0,1]:
                        t=ix[i,j];g=data['groups'][t];a,n=data['starts'][g],data['lengths'][g];x[i,j]-=logsumexp(lp[[c for c in range(a,a+n) if c!=t]])
            if link=='fixed_beta_one':X=np.stack([np.ones_like(x),first,np.repeat(trial[:,None],2,axis=1)],axis=2);eta=X@coef+x;beta=None
            else:X=np.stack([np.ones_like(x),x,first,np.repeat(trial[:,None],2,axis=1)],axis=2);eta=X@coef;beta=1
            mask=cal;Y=y
        q=expit(eta);loss=np.logaddexp(0,eta)-Y*eta;losses[key]=loss if loss.ndim==1 else loss.sum(axis=1)
        gradient=X[mask].reshape(-1,len(coef)).T@(q[mask]-Y[mask]).ravel()
        if beta is not None and coef[beta]<1e-8 and gradient[beta]>0:gradient[beta]=0
        pg=float(max(abs(gradient)))
        if pg>1.01e-5:raise ValueError(('Response gradient',key,pg))
        rec={k:r[k] for k in ['sampling','model','link']}|{'projected_gradient':pg,'evaluation':{}}
        for name,mask in splits.items():
            if link=='paired_discordant':mm=mask&discord;ev={'trials':int(mm.sum()),'logloss':float(loss[mm].mean())}
            else:ev={'trials':int(mask.sum()),'sum_binary_logloss_per_trial':float(loss[mask].sum()/mask.sum()),'faithful_logloss':float(loss[mask,0].mean()),'deletion_logloss':float(loss[mask,1].mean()),'faithful_Brier':float(((q[mask,0]-y[mask,0])**2).mean()),'deletion_Brier':float(((q[mask,1]-y[mask,1])**2).mean()),'predicted_rates':q[mask].mean(axis=0).tolist(),'observed_rates':y[mask].mean(axis=0).tolist()}
            rec['evaluation'][name]=ev
        if link!='paired_discordant':
            bins=[]
            for alt in [0,1]:
                ind=np.flatnonzero(splits['primary_both']);ind=ind[np.argsort(q[ind,alt])]
                for b,ids in enumerate(np.array_split(ind,5)):bins.append({'alternative':alt,'bin':b,'n':len(ids),'prediction':float(q[ids,alt].mean()),'observed':float(y[ids,alt].mean())})
            rec['calibration_bins']=bins
            shape=np.array(['CVC' if r['C']=='2' else ('CVCC' if r['position']=='1' else 'CCVC') for r in rows]);m=splits['primary_both'];a=m&(shape=='CVCC');b=m&(shape=='CVC')
            rec['primary_CVCC_minus_CVC']={'observed':(y[a].mean(axis=0)-y[b].mean(axis=0)).tolist(),'predicted':(q[a].mean(axis=0)-q[b].mean(axis=0)).tolist()}
        out['fits'].append(rec)
    for sampling in ['corrected_left','uncorrected_left'] if variant=='left' else ['corrected','uncorrected']:
        for link in ['log_probability','fixed_beta_one','logit_probability','paired_discordant']:
            mask=splits['primary_both']&(discord if link=='paired_discordant' else True)
            for rival in ['current','zero','expanded','sublexical']:
                delta=losses[f'{sampling}|retained|{link}']-losses[f'{sampling}|{rival}|{link}']
                out['contrasts'].append({'sampling':sampling,'retained_minus_rival':rival,'link':link,**crossed_interval(rows,mask,delta,resamples)})
    out['uncertainty_scope']='Crossed participant/consonant-cluster resampling conditional on fixed fitted grammars and links; does not include training uncertainty.'
    write('russian_response_'+variant+'.json',out,work)
    print(variant,len(out['fits']),len(out['contrasts']),flush=True)
    return out


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--inputs',type=Path,required=True);parser.add_argument('--work',type=Path,required=True);parser.add_argument('--phase',choices=['prepare','replay','all'],default='all');parser.add_argument('--variant',choices=['all','no_overlap','left'],default='all');parser.add_argument('--resamples',type=int,default=2000);args=parser.parse_args()
    args.work.mkdir(parents=True,exist_ok=True)
    if args.resamples<2000:raise ValueError('At least 2000 resamples required')
    if args.phase in ['prepare','all']:prepare(args.inputs,args.work)
    if args.phase in ['replay','all']:
        checked_inputs(args.inputs);data=np.load(args.work/'design.npz');parameters=read('russian_fitted_parameters.json')
        design_check(data,args.work);checks=lexical_replay(data,parameters,args.work);write('russian_lexical_replay.json',{'checks':checks,'fits':len(checks)},args.work)
        response_replay(data,parameters,args.work,args.resamples,args.variant)

if __name__=='__main__':main()
