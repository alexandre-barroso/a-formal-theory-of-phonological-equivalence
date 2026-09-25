import hashlib
import itertools
import json
import random
from . import certificate
from . import identification_sample as N
from .evaluate import activation, coefficients

names=('IDENT_PREFIX','IDENT_STEM','DEP','AGREE','NOGEM','MAX');symbols='pbtdkg'
def seg(s):return ('obs',symbols.index(s)//2,symbols.index(s)%2) if s in symbols else ('other',s)
def present(x):return x is not None
def ob(x):return x is not None and x[0]=='obs'
def nxt(cells,side):
 for cell in cells:
  if present(cell[side]):return cell
 return (None,None)
def bad(x,y,k):return ob(x) and ob(y) and (x[2]!=y[2] if k==0 else x[1:]==y[1:])
def matrix(c1,c2,tail,h,key):
 x,y,z=key;ref=[seg('a'),seg(c1),None,seg(c2)]+list(map(seg,tail));cur=[seg('a'),('obs',seg(c1)[1],x),seg('i') if z else None,('obs',seg(c2)[1],y)]+list(map(seg,tail));cells=list(zip(ref,cur));out=[[0,0] for _ in names]
 for q,(r,s) in enumerate(cells):
  out[0 if q<2 else 1][0]+=int(ob(r) and ob(s) and r[2]!=s[2]);out[2][0]+=int(not present(r) and present(s));out[5][0]+=int(present(r) and not present(s))
  for k in range(2):
   a=bad(r,nxt(cells[q+1:],0)[0],k)
   curpartner=nxt(cells[q+1:],0 if h[k]=='S' else 1)[1]
   b=bad(s,curpartner,k)
   out[3+k][0]+=int(a and b);out[3+k][1]+=int(not a and b)
 return out

def run():
 keys=list(itertools.product(range(2),repeat=3))
 tails=('', 'a', 'aa', 'abg', 'ap', 'b', 'g', 'p', 'pap', 'pb', 't')
 sigma=N.FL.make_sigma();checks=0;fresh=0;digest=hashlib.sha256()
 for c1,c2,h,tail in itertools.product(symbols,symbols,('RR','RS','SR','SS'),tails):
  ds=N.factorisation(*h);ref,cands=N.build(c1,c2,tail);acts=activation(sigma,ref,ds)
  for key,cand in cands:
   expected=matrix(c1,c2,tail,h,key)
   got=coefficients(sigma,ref,cand,ds,acts)
   assert expected==[list(got[k]) for k in names],(c1,c2,tail,h,key)
   digest.update(json.dumps([c1,c2,tail,h,key,expected],ensure_ascii=False,separators=(',',':')).encode())
   checks+=1
 assert checks==12672
 rng=random.Random(201126);lengths=[0,1,2,4,9,17,33,65]
 for trial in range(32):
  c1=rng.choice(symbols);c2=rng.choice(symbols);h=rng.choice(['RR','RS','SR','SS']);length=lengths[trial%len(lengths)]
  tail=''.join(rng.choice(symbols+'aiuz') for _ in range(length));ds=N.factorisation(*h);ref,cands=N.build(c1,c2,tail);acts=activation(sigma,ref,ds)
  for key,cand in cands:
   expected=matrix(c1,c2,tail,h,key)
   got=coefficients(sigma,ref,cand,ds,acts)
   assert expected==[list(got[k]) for k in names],(trial,key)
   digest.update(json.dumps([c1,c2,tail,h,key,expected],ensure_ascii=False,separators=(',',':')).encode())
   fresh+=1
 assert fresh==256
 out={'native_coefficient_matrices':checks,'seeded_long_tail_matrices':fresh,'coordinates_per_matrix':12,'seed':201126,'tail_lengths':lengths,'matrix_sha256':digest.hexdigest(),'all_pass':True}
 certificate.write('learning_tail.json',out)
 print(json.dumps(out))
 return out

if __name__=='__main__':
 run()
