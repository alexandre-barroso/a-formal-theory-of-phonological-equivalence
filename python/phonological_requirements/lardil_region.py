from pathlib import Path
from dataclasses import replace
from fractions import Fraction as F
import itertools,json,sys,datetime,hashlib
from . import paths,certificate
spec={'inputs': [{'tokens': ['w', 'i', 'w', 'a', 'l', 'a'], 'output': ['w', 'i', 'w', 'a', 'l']},
            {'tokens': ['th', 'u', 'r', 'a', 'r', 'a', 'ŋ'], 'output': ['th', 'u', 'r', 'a', 'r', 'a']},
            {'tokens': ['ŋ', 'a', 'w', 'u', 'ŋ', 'a', 'w', 'u'], 'output': ['ŋ', 'a', 'w', 'u', 'ŋ', 'a']}],
 'vowels': ['a', 'i', 'u'],
 'nonapical': ['w', 'th', 'ŋ']}
OBS=[(tuple(x['tokens']),tuple(x['output'])) for x in spec['inputs']]
V=set(spec['vowels']);K=set(spec['nonapical']);MODES={'D':(True,True),'R':(False,False),'L':(True,False),'T':(False,True)}
NAMES=['APO','KDEL','MAX_V','MAX_K']
def generate(s):
 return itertools.product(*[(x,None) if x in V|K else (x,) for x in s])
def surface(s):return tuple(x for x in s if x is not None)
def read(s,i,rule,mode):
 vs=[j for j in range(i-1,-1,-1) if s[j] in V]
 rs=[j for j in range(i+1,len(s)) if s[j] is not None]
 pv2=vs[1] if len(vs)>=2 else None;n=rs[0] if rs else None
 lc=pv2 is not None if rule=='APO' else True;rc=n is None
 cl,cr=MODES[mode];p=s[i] is not None and (lc or not cl) and (rc or not cr)
 a=s[i] in (V if rule=='APO' else K) and lc and rc
 subject=((pv2,) if cl and rule=='APO' else ())+((n,) if cr else ())+(i,)
 return a,p,subject
def coeff(ref,c,modes,sub=False):
 out=[]
 for rule,mode in zip(NAMES[:2],modes):
  before=[read(ref,i,rule,mode) for i in range(len(ref))];subjects={s for a,p,s in before if a and p};old=new=0
  for i in range(len(ref)):
   a,p,s=read(c,i,rule,mode);a0,p0,_=before[i];ret=s in subjects if sub else a0 and p0
   old+=int(p and ret);new+=int(p and not ret and a)
  out.append([old,new])
 out.extend([[sum(x in cls and c[i] is None for i,x in enumerate(ref)),0] for cls in (V,K)])
 return out
records={};changes=0;count=0
for modes in itertools.product(MODES,repeat=2):
 rows=[]
 for ref,target in OBS:
  candidates=[]
  for i,c in enumerate(generate(ref)):
   b=coeff(ref,c,modes);s=coeff(ref,c,modes,True);changes+=b!=s;count+=1
   candidates.append({'i':i,'state':c,'surface':surface(c),'baseline':b,'subject':s})
  rows.append({'input':ref,'target':target,'fiber':[c['i'] for c in candidates if c['surface']==target],'rows':candidates})
 records[''.join(modes)]=rows
from phonological_requirements.core import ABSENT,And,Decl,Feat,Not,Or_,Present,Resolves,Slot,TRUE
from phonological_requirements.frag_seq import make_sigma,build,candidates as native_candidates,WORD,T
from phonological_requirements.evaluate import activation,marked_subjects,coefficients
alphabet={x:tuple(c for c,cls in [('V',V),('K',K)] if x in cls) for ref,_ in OBS for x in ref}
sigma0=make_sigma(alphabet)
sigma=replace(sigma0,features={x:{**d,'nuclear':x in V} for x,d in sigma0.features.items()})
pv1=Slot('p1','Or','subject',kind='step',relation='succ',scope=WORD,direction=-1,filter='nuclear')
pv2=Slot('p2','Or','subject',kind='stepof',relation='succ',scope=WORD,direction=-1,filter='nuclear',of='p1',tier='seg')
nx=Slot('r','Or','subject',kind='step',relation='succ',scope=WORD,direction=1,filter='present')
def declarations(modes):
 ds={}
 for rule,mode in zip(NAMES[:2],modes):
  cl,cr=MODES[mode];lt=Resolves('p2') if rule=='APO' else TRUE;rt=Not(Resolves('r'))
  parts=([lt] if cl and rule=='APO' else [])+([rt] if cr else [])
  consequence=Or_((Not(And(tuple(parts))),Not(Present('t')))) if parts else Not(Present('t'))
  ds[rule]=Decl(rule,'Or',(T,pv1,pv2,nx),And((Feat('is_'+('V' if rule=='APO' else 'K'),'t',True),lt,rt)),consequence,scope=WORD)
 for cls in ('V','K'):
  ds['MAX_'+cls]=Decl('MAX_'+cls,'Or',(T,),Feat('is_'+cls,'t',True,where='reference'),Present('t'),kind='faithfulness')
 return ds
comparisons=0
for modes,data in records.items():
 ds=declarations(modes);assert all(d.well_typed(sigma)[0] for d in ds.values())
 for item in data:
  ref=build(item['input']);acts=activation(sigma,ref,ds);subjects=marked_subjects(sigma,ref,ds)
  nc=list(native_candidates(ref,{x:[x,ABSENT] for x in V|K}));assert len(nc)==len(item['rows'])
  for candidate,row in zip(nc,item['rows']):
   assert tuple(candidate.real[n] for n in candidate.order['seg'] if candidate.real[n]!=ABSENT)==tuple(row['surface'])
   for variant,su in [('baseline',None),('subject',subjects)]:
    actual=coefficients(sigma,ref,candidate,ds,acts,subjects=su)
    assert [list(actual[x]) for x in NAMES]==row[variant],(modes,item['input'],row['i'],variant,actual,row[variant])
    comparisons+=len(NAMES)
ref=OBS[2][0];after_apo=ref[:-1]+(None,);after_both=ref[:-2]+(None,None)
assert read(ref,7,'APO','R')[0] and not read(ref,6,'KDEL','R')[0]
assert read(after_apo,6,'KDEL','R')[0] and not read(after_apo,5,'APO','R')[0]
assert read(after_both,5,'APO','R')[0]
out=certificate.write('lardil_region_coefficients.json',records)
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'modes':16,'inputs':3,'records':count,'native_coefficient_pairs':comparisons,'subject_changed_records':changes,'fibers':[r['fiber'] for r in records['RR']],'R4_cycle':['APO creates KDEL at origin6','KDEL creates APO at origin5 with three remaining vowels'],'source':'frischoffRasin2026absenceCruciallySimultaneous','source_pages':[13,14],'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}
certificate.write('lardil_region.json',report);print(json.dumps(report))
