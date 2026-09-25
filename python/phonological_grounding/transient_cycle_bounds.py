from pathlib import Path
import sys,itertools,json,hashlib
from fractions import Fraction as F
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from phonological_requirements.core import *
from phonological_requirements.frag_seq import make_sigma,build,candidates,rule_decl,faith_decls,surface
from phonological_requirements.evaluate import activation,coefficients,score,marked_subjects
from phonological_requirements.interaction import locus_graph
from dataclasses import replace

A={'x':{'X','C'},'y':{'Y','C'},'c':{'C'},'v':{'V'},'i':{'I'}}
sg=make_sigma(A)
base={'MUT_FRONT':rule_decl('MUT_FRONT','X',(),('I',),'y','retain'),'DELETE_V':rule_decl('DELETE_V','V',(),('C',),None,'retain')}
base.update(faith_decls(A,[('x','y'),('V',None)]))
base.pop('IDENT_x_y')
base['IDENT_x_y']=Decl('IDENT_x_y','Or',(Slot('t','Or','subject',kind='anchor'),),Feat('is_X','t',True,where='reference'),Not(Feat('sym','t','y')),kind='faithfulness')
cluster=rule_decl('MUT_CLUSTER','X',(),('C',),'y','retain')
exists=replace(cluster,consequence=And((Resolves('r1'),Feat('sym','t','y'))))
Ws={'MUT_FRONT':4,'MUT_CLUSTER':4,'DELETE_V':3,'IDENT_x_y':2,'MAX_V':1}; lam=F(1,4)
battery={'xc': 'yc', 'xi': 'yi', 'xv': 'xv', 'xvc': 'xc', 'x': 'x', 'c': 'c', 'v': 'v', 'i': 'i'}
res={'grammars':{},'counts':{}}
checks=0
for variant in ['plain','cluster','exists_cluster']:
 ds=base|({} if variant=='plain' else {'MUT_CLUSTER':cluster if variant=='cluster' else exists})
 assert all(d.well_typed(sg)[0] for d in ds.values())
 rows={}
 for inp in battery:
  ref=build(list(inp)); acts=activation(sg,ref,ds); subs=marked_subjects(sg,ref,ds)
  cs=list(candidates(ref,{'x':['x','y'],'v':['v',ABSENT]})); rs=[]
  for c in cs:
   co=coefficients(sg,ref,c,ds,acts,subjects=subs)
   val=score(co,{k:Ws[k] for k in ds},lam)
   rs.append({'surface':surface(c),'score':str(val),'coeff':co})
   checks+=1
  best=min(F(r['score']) for r in rs); wins=[r['surface'] for r in rs if F(r['score'])==best]
  rows[inp]={'candidates':rs,'winners':wins,'target':battery[inp],'matches':wins==[battery[inp]]}
 if variant!='plain': assert all(r['matches'] for r in rows.values())
 res['grammars'][variant]=rows
ref=build(['x','c']); gone=ref.with_real(ref.nodes('seg')[1],ABSENT)
res['existence_probe']={}
for name,d in [('anchor',cluster),('exists',exists)]:
 ds={d.name:d}; acts=activation(sg,ref,ds); subs=marked_subjects(sg,ref,ds)
 n=ref.nodes('seg')[0]
 res['existence_probe'][name]={'reference_reader':read(sg,ref,ref,d,n).triple(),'gone_reader':read(sg,ref,gone,d,n).triple(),'canonical_coeff':coefficients(sg,ref,gone,ds,acts,subjects=subs),'locus_coeff':coefficients(sg,ref,gone,ds,acts)}
t=Slot('t','Or','subject',kind='anchor'); phi=Feat('is_X','t',True)
taut=Or_((phi,Not(phi)))
ds={n:Decl(n,'Or',(t,),TRUE,taut) for n in ['A','B']}
ref=build(['x']); cs=list(candidates(ref,{'x':['x','y']}))
keys,edges,shared,inexact=locus_graph(sg,ref,cs,ds)
assert edges and all(read(sg,ref,c,d,ref.nodes('seg')[0]).pressure==0 for c in cs for d in ds.values())
res['graph']={'potential_edges':sorted(map(str,edges)),'positive_pressure_repair_events':0,'custom_terms':False}
cycle=[]; cc=0
for n in range(0,15):
 rows=[]
 for s in itertools.product([0,1],repeat=n):
  m=sum(s); u=sum(not s[j] and not s[(j-1)%n] for j in range(n))
  rows.append((s,m,u))
 for r,w in [(F(0),F(0)),(F(0),F(1)),(F(1),F(0)),(F(1),F(1)),(F(1,3),F(2,3)),(F(2),F(1))]:
  sc=[r*m+w*u for s,m,u in rows]; b=min(sc); winners=[s for (s,m,u),v in zip(rows,sc) if v==b]
  if 0<r<w:
   expected=[s for s,m,u in rows if m==(n+1)//2 and u==0]
   assert set(winners)==set(expected)
   if n>=2: assert len(winners)==(n if n%2 else 2)
  if r==0<w: assert set(winners)=={s for s,m,u in rows if u==0}
  if w==0<r: assert winners==[(0,)*n]
  cc+=len(rows)
  cycle.append({'n':n,'r':str(r),'w':str(w),'minimum':str(b),'winner_count':len(winners),'all_apply_wins':(1,)*n in winners})
res['cycles']=cycle; res['counts']={'native_candidates':checks,'cycle_candidate_score_checks':cc,'cycle_systems':len(cycle)}
res['counterexamples']={'r_zero':{'k':3,'r':0,'w':1,'winner_count':4,'includes_all_apply':True},'self_loop':{'k':1,'r':1,'w':2,'unique_winner':'all apply'},'shared_site':{'k':2,'independent_sets_allowed':['00','11'],'r':1,'w':2,'scores':[4,2],'unique_winner':'11'},'new_only_strict':{'w':1,'lambda':0,'old_s':0,'new_s':1,'old_t':0,'new_t':0,'scores':[0,0]}}
print(json.dumps({'counts':res['counts'],'battery':{k:{x:r['winners'] for x,r in v.items()} for k,v in res['grammars'].items()},'existence_probe':res['existence_probe'],'graph':res['graph'],'counterexamples':res['counterexamples']},ensure_ascii=False,indent=2))
