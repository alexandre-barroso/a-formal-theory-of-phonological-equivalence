from pathlib import Path
import json
import numpy as np
from . import certificate, paths
from .products import gua_products, gua_observations
from .indep_gua import ALPHABET, SCHEMATA
from . import frag_gua as fg
from .evaluate import activation, marked_subjects, coefficients

class Reconstruction:
 def __init__(self,p):
  self.p=p; self.syms=list(ALPHABET)+sorted(set(p.reference)-set(ALPHABET)); self.d={s:i for i,s in enumerate(self.syms)}
  self.ref=np.array([self.d[s] for s in p.reference],dtype=np.int16)
  self.present=np.array([s!='∅' for s in self.syms]); self.nuclear=np.array([s in 'aɜɛeɪiɔoʊu' for s in self.syms])
  self.quality=np.array([-1,0,0,1,1,2,2,3,3,4,4,2,4]+[-1]*(len(self.syms)-13))
  self.atr=np.array([-1,0,1,0,1,0,1,0,1,0,1,-1,-1]+[-1]*(len(self.syms)-13))
  self.high=np.array([s in ('ɪ','i','ʊ','u') for s in self.syms]); self.n=len(p.reference)
  self.active=self.bits(self.ref[None,:])[0][0]
 def bits(self,s):
  b,n=s.shape; pr=self.present[s]; nu=self.nuclear[s]; hi=self.high[s]; at=self.atr[s]; qu=self.quality[s]
  C=np.zeros((b,9,n),bool); P=np.zeros_like(C)
  C[:,0:4,:]=True; P[:,0,:]=~pr
  P[:,1,:]=nu & self.nuclear[self.ref] & (at!=self.atr[self.ref])
  P[:,2,:]=pr & (qu>=0) & (self.quality[self.ref]>=0) & (qu!=self.quality[self.ref])
  P[:,3,:]=pr & (nu!=self.nuclear[self.ref])
  row=np.arange(b)
  for q in range(n):
   nr=np.full(b,-1); nl=np.full(b,-1); src=np.full(b,-1)
   for j in range(q+1,n):
    nr=np.where((nr<0)&pr[:,j],j,nr)
    if self.p.words[j]>self.p.words[q] and self.p.phrase(j)==self.p.phrase(q): src=np.where((src<0)&nu[:,j],j,src)
   for j in range(q-1,-1,-1): nl=np.where((nl<0)&pr[:,j],j,nl)
   nr=np.where(pr[:,q],nr,-1); nl=np.where(pr[:,q],nl,-1)
   last=nu[:,q].copy()
   for j in range(q+1,n):
    if self.p.words[j]==self.p.words[q]: last &= ~nu[:,j]
   C[:,4,q]=last&(src>=0)&(at[row,src]==1); P[:,4,q]=nu[:,q]&(at[:,q]!=1)
   words=np.array(self.p.words); phrases=np.array([self.p.phrase(i) for i in range(n)])
   cross=(nr>=0)&(words[nr]==words[q]+1)&(phrases[nr]==phrases[q])
   C[:,5,q]=nu[:,q]&~hi[:,q]&cross&nu[row,nr]&~hi[row,nr]
   P[:,5,q]=pr[:,q]&((nr<0)|(s[:,q]!=s[row,nr]))
   nb=np.zeros(b,bool)
   for near in (nr,nl): nb |= (near>=0)&(np.abs(words[near]-words[q])==1)&(phrases[near]==phrases[q])&nu[row,near]&~hi[row,near]
   C[:,6,q]=nu[:,q]&hi[:,q]&nb; P[:,6,q]=nu[:,q]
   C[:,7,q]=nu[:,q]&hi[:,q]&(nl>=0)&(words[nl]+1==words[q])&(phrases[nl]==phrases[q])&nu[row,nl]&hi[row,nl]
   P[:,7,q]=pr[:,q]
   C[:,8,q]=self.nuclear[self.ref[q]] and (q==0 or words[q-1]!=words[q])
   P[:,8,q]=pr[:,q]&(qu[:,q]>=0)&((qu[:,q]!=self.quality[self.ref[q]])|(nu[:,q]&(at[:,q]!=self.atr[self.ref[q]])))
  return C&P,C,P
 def coefficients(self,s):
  cp,c,p=self.bits(s); out=np.zeros((len(s),9,2),dtype=np.int16)
  out[:,:,0]=cp.sum(axis=2)
  out[:,4:8,0]=(p[:,4:8]&self.active[4:8]).sum(axis=2)
  out[:,4:8,1]=(p[:,4:8]&~self.active[4:8]&c[:,4:8]).sum(axis=2)
  return out
 def decode(self,s): return tuple(self.syms[i] for i in s)
 def correct(self,s,allowed):
  correct=np.zeros(len(s),bool)
  for obs in allowed:
   lens=np.zeros(len(s),int); ok=np.ones(len(s),bool)
   for q in range(self.n):
    for val in np.unique(s[:,q]):
     seg=self.syms[val]; mask=s[:,q]==val
     if seg=='∅': continue
     starts=lens[mask]; ok[mask]&=np.array([obs[k:k+len(seg)]==seg for k in starts]); lens[mask]+=len(seg)
   correct |= ok&(lens==len(obs))
  return correct

def typed_coefficients(r,s):
 cs=r.coefficients(s);_,c,p=r.bits(s);pr=r.present[s];n=len(s)
 words=np.array(r.p.words);phrases=np.array([r.p.phrase(q) for q in range(r.n)])
 pair=np.zeros((n,2),np.int16)
 assert r.present[r.ref].all()
 for q in range(r.n):
  nr=np.full(n,-1)
  for j in range(q+1,r.n):nr=np.where((nr<0)&pr[:,j],j,nr)
  nr=np.where(pr[:,q],nr,-1)
  defined=(nr>=0)&(words[nr]==words[q]+1)&(phrases[nr]==phrases[q])
  pressure=defined&p[:,5,q];retained=r.active[5,q]&(nr==q+1)
  pair[:,0]+=pressure&retained;pair[:,1]+=pressure&~retained&c[:,5,q]
 cs[:,5,:]=pair
 return cs

def run(mode):
 assert mode in ('appendix','subject')
 rng=np.random.default_rng(718944);cases=[];obs=gua_observations();checks=0
 w0=np.array([3,1,1,2,2,4,4,4,4]);w1=np.array([-4,0,-2,-2,0,0,0,0,0])
 for _,p in gua_products():
  r=Reconstruction(p);eligible=[q for q in range(p.n) if r.nuclear[r.ref[q]] or p.reference[q] in ('j','w')]
  total=13**len(eligible);reconstruct=typed_coefficients if mode=='subject' else lambda r,s:r.coefficients(s)
  sigma=fg.make_sigma();ds=fg.declarations('typed','dynamic',fg.NEXT_WORD,None,'stop')
  ref=fg.struct_from_segments(p.reference,p.words,p.phrase_of_word);acts=activation(sigma,ref,ds);subjects=marked_subjects(sigma,ref,ds)
  random=np.repeat(r.ref[None,:],100,axis=0);random[:,eligible]=rng.integers(0,13,(100,len(eligible)))
  for s,cs in zip(random,reconstruct(r,random)):
   st=r.decode(s)
   if mode=='subject':
    candidate=fg.struct_from_segments(st,p.words,p.phrase_of_word)
    cf=coefficients(sigma,ref,candidate,ds,acts,subjects=subjects)
    expected=[list(cf[k]) for k in SCHEMATA]
   else:expected=[list(x) for x in p.coefficients(st,p.activation_bits())]
   assert cs.tolist()==expected,(p.id,st)
   checks+=1
  unique={};good=[]
  for lo in range(0,total,20000):
   inds=np.arange(lo,min(lo+20000,total));s=np.repeat(r.ref[None,:],len(inds),axis=0)
   for i,q in enumerate(reversed(eligible)):s[:,q]=(inds//13**i)%13
   cs=reconstruct(r,s);correct=r.correct(s,obs[p.id]['allowed'])
   for idx in np.flatnonzero(correct):good.append({'index':int(inds[idx]),'state':list(r.decode(s[idx])),'coefficients':cs[idx].tolist()})
   keys=np.concatenate([cs.reshape(len(s),18),correct[:,None]],axis=1)
   rows,first,counts=np.unique(keys,axis=0,return_index=True,return_counts=True)
   for row,idx,count in zip(rows,first,counts):
    key=tuple(int(x) for x in row)
    if key in unique:unique[key][0]+=int(count)
    else:unique[key]=[int(count),list(r.decode(s[idx]))]
  assert sum(v[0] for v in unique.values())==total and good
  records=[{'coefficients':np.array(k[:18]).reshape(9,2).tolist(),'correct':bool(k[18]),'multiplicity':v[0],'state':v[1]} for k,v in sorted(unique.items())]
  goal=min(good,key=lambda g:int(w0@np.array(g['coefficients'])[:,0]))
  gc=np.array(goal['coefficients']);minimum_a=None;minimum_endpoint=None
  for row in records:
   if row['correct']:continue
   diff=np.array(row['coefficients'])-gc
   a=int(w0@diff[:,0]);b=int(w1@diff[:,0]+w0@diff[:,1]);c=int(w1@diff[:,1])
   assert a>0 and 2*a+b>=0 and c==0,(p.id,row['state'],a,b,c)
   minimum_a=a if minimum_a is None else min(minimum_a,a)
   minimum_endpoint=2*a+b if minimum_endpoint is None else min(minimum_endpoint,2*a+b)
  cases.append({'id':p.id,'records':records,'total':total,'eligible':eligible,'correct_fiber':good,'goal':goal,'minimum_a':minimum_a,'minimum_twice_endpoint':minimum_endpoint})
  print(json.dumps({'id':p.id,'candidates':total,'classes':len(records),'correct':len(good)}),flush=True)
 assert sum(x['total'] for x in cases)==15967796 and checks==800
 out={'mode':mode,'cases':cases,'candidates':15967796,'classes':sum(len(x['records']) for x in cases),'native_coefficient_checks':checks,'seed':718944,'all_margins_pass':True}
 certificate.write('productive_region_'+mode+'.json',out)
 print(json.dumps({k:v for k,v in out.items() if k!='cases'}))
 return out
