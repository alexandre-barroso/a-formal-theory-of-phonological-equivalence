from pathlib import Path
from fractions import Fraction as F
import sys,itertools,json
from . import certificate, paths
from phonological_requirements import identification_sample as N
from phonological_requirements.evaluate import activation,coefficients,score
S=N.FL.make_sigma()
checks=rows=0
lamlist=[F(1,100),F(1,8),F(1,3),F(1,2),F(7,8),F(99,100)]
keys=list(itertools.product((0,1),repeat=3))
def pred(v1,v2,same,h,c):
 x,y,z=c
 return y==v2 and ((x==v2 and not z) if not same else ((x==v1 and z) if h[1]=='R' else (x!=v1 and (h[0]=='R' or not z))) if v1==v2 else ((x==v1 and z) if h[0]=='R' else (x!=v1 and (h[1]=='R' or not z))))
for c1,c2,h,tail in itertools.product('pbtdkg','pbtdkg',('RR','RS','SR','SS'),('','a','apbtg')):
 ref,cands=N.build(c1,c2,tail);D=N.factorisation(*h);a=activation(S,ref,D)
 coeff=[coefficients(S,ref,c,D,a) for _,c in cands]
 expected=[key for key in keys if pred('pbtdkg'.index(c1)%2,'pbtdkg'.index(c2)%2,N.PLACE[c1]==N.PLACE[c2],h,key)]
 for lam in lamlist:
  W={'IDENT_PREFIX':lam*(1-lam),'IDENT_STEM':2,'DEP':lam,'AGREE':1,'NOGEM':1,'MAX':17}
  scores=[score(c,W,lam) for c in coeff];best=min(scores);got=[key for key,s in zip(keys,scores) if s==best]
  assert got==expected,(c1,c2,h,tail,lam,got,expected)
  rows+=len(cands);checks+=1
out={'native_minimizer_checks':checks,'native_scores':rows,'lambda_values':list(map(str,lamlist)),'all_pass':True,'scope':'finite native regression of universal Boolean attenuation witness, not proof of arbitrary native tails'}
certificate.write("learning_invariance.json",out);print(json.dumps(out))
