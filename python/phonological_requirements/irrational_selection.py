import dataclasses,hashlib,itertools,json,math,random
from . import certificate, paths
M=paths.REPO
from .frag_seq import make_sigma,rule_decl,faith_decls,build,candidates
from .evaluate import activation,coefficients
from .core import read
@dataclasses.dataclass(frozen=True)
class Exact:
 a:int=0
 b:int=0
 def __add__(self,other):
  if isinstance(other,int): other=Exact(other)
  return Exact(self.a+other.a,self.b+other.b)
 __radd__=__add__
 def __neg__(self): return Exact(-self.a,-self.b)
 def __sub__(self,other): return self+-other
 def __lt__(self,other):
  if isinstance(other,int): other=Exact(other)
  a,b=(other-self).a,(other-self).b
  if a>=0 and b>=0:return a+b>0
  if a<=0 and b<=0:return False
  return a*a>2*b*b if a>0 else 2*b*b>a*a
 def __le__(self,other):return self==other or self<other
zero=Exact()
def unary(x,y):return Exact(1) if x=='a' and y=='b' else Exact(0,1) if x=='b' and y=='a' else zero
def score(u,v):return sum((unary(x,y) for x,y in zip(u,v)),zero)+8*sum(x!=y for x,y in zip(v,v[1:]))
def dp(u):
 a=b=zero
 for x in u:a,b=min(a,b+8)+unary(x,'a'),min(b,a+8)+unary(x,'b')
 return min(a,b)
def word(n):return ''.join('b'+'a'*(math.isqrt(2*j*j)-math.isqrt(2*(j-1)**2)) for j in range(1,n+1))
def balance(u):return Exact(-u.count('a'),u.count('b'))
alpha={'a':{'A'},'b':{'B'}};sig=make_sigma(alpha)
decls={'AB':rule_decl('AB','B',('A',),(),'a','discharge'),'BA':rule_decl('BA','A',('B',),(),'b','discharge')}
decls.update(faith_decls(alpha,[('A','b'),('B','a')]))
counts={'native_candidates':0,'native_readers':0,'full_argmin_sets':0,'long_candidates':0,'separating_pairs':0,'prefix_balances':0}
mutants={'omit_switch':False,'swap_identity':False,'reference_switch':False,'strict_tie':False}
records=[]
def check_native(u,v,ref,act):
 out=build(v);coef=coefficients(sig,ref,out,decls,act)
 exact=Exact(8*(sum(coef['AB'])+sum(coef['BA']))+sum(coef['IDENT_A_b']),sum(coef['IDENT_B_a']))
 assert exact==score(u,v)
 for i,node in enumerate(ref.nodes('seg')):
  rp=u[i-1] if i else None;cp=v[i-1] if i else None;x=u[i];y=v[i]
  for name,target,prev in [('AB','b','a'),('BA','a','b')]:
   obs=read(sig,ref,out,decls[name],node)
   expected=(y==target and cp==prev,True,cp!=prev or y!=target)
   assert obs.triple()==expected,(u,v,i,name,obs.triple(),expected)
   assert act[name][node]==(x==target and rp==prev)
   counts['native_readers']+=1
  for name,target,repair in [('IDENT_A_b','a','b'),('IDENT_B_a','b','a')]:
   obs=read(sig,ref,out,decls[name],node)
   assert obs.triple()==(x==target,True,y!=repair)
   counts['native_readers']+=1
 no_switch=sum((unary(x,y) for x,y in zip(u,v)),zero)
 mutants['omit_switch']|=exact!=no_switch
 mutants['reference_switch']|=exact!=no_switch+8*sum(x!=y for x,y in zip(u,u[1:]))
 swapped=Exact(sum(x=='b' and y=='a' for x,y in zip(u,v))+8*sum(x!=y for x,y in zip(v,v[1:])),sum(x=='a' and y=='b' for x,y in zip(u,v)))
 mutants['swap_identity']|=exact!=swapped
 return exact
for n in range(7):
 for us in itertools.product('ab',repeat=n):
  u=''.join(us);ref=build(u);act=activation(sig,ref,decls)
  scored=[]
  for cand in candidates(ref,{'a':['a','b'],'b':['a','b']}):
   v=''.join(cand.real[node] for node in ref.nodes('seg'))
   val=check_native(u,v,ref,act);scored.append((v,val));counts['native_candidates']+=1
  assert len(scored)==2**n and len({v for v,_ in scored})==2**n
  best=min(x for _,x in scored);assert dp(u)==best
  winners=[v for v,c in scored if c==best]
  constants=[y*n for y in 'ab' if score(u,y*n)==best]
  bounds=[balance(u[:j]) for j in range(n+1)]
  if all(Exact(-8)<=t<=Exact(8) for t in bounds):
   assert ('a'*n in winners)==(balance(u)<=zero)
  counts['full_argmin_sets']+=1
  records.append({'input':u,'min':[best.a,best.b],'winners':winners})
mutants['strict_tie']=dp('')==score('','') and not balance('')<zero
rng=random.Random(20260920)
for _ in range(128):
 n=rng.randrange(20,81);u=''.join(rng.choice('ab') for _ in range(n));v=''.join(rng.choice('ab') for _ in range(n));ref=build(u);act=activation(sig,ref,decls)
 check_native(u,v,ref,act);counts['long_candidates']+=1
residues=[balance(word(n)) for n in range(65)]
assert len(set(residues))==65
witnesses=[]
for n,m in itertools.combinations(range(1,65),2):
 if residues[m]<residues[n]:n,m=m,n
 k=next(k for k in range(1,20000) if -residues[m]<balance(word(k))+Exact(-1)<-residues[n])
 z=word(k)+'a'
 for i in [n,m]:
  u=word(i)+z
  assert dp(u)==min(Exact(0,u.count('b')),Exact(u.count('a')))
  assert dp(u)-dp(word(i))==min(Exact(0,z.count('b'))+residues[i],Exact(z.count('a')))
  b=zero
  for x in u:
   b+=Exact(0,1) if x=='b' else Exact(-1)
   assert Exact(-1)<=b<Exact(2,1)
   counts['prefix_balances']+=1
 assert score(word(n)+z,'a'*len(word(n)+z))==dp(word(n)+z)
 assert score(word(m)+z,'a'*len(word(m)+z))!=dp(word(m)+z)
 assert dp(word(n)+z)-dp(word(n))<dp(word(m)+z)-dp(word(m))
 witnesses.append({'n':n,'m':m,'k':k});counts['separating_pairs']+=1
assert all(mutants.values())
result={'all_pass':True,'counts':counts,'seed':20260920,'mutants_detected':mutants,'lambda_one_activation_mutation':'equivalent: pressure implies current activation in this concrete discharge grammar, proved by native_local_exact','sqrt2':'exact Z[sqrt2] coefficient comparison','residues':65,'max_suffix_index':max(w['k'] for w in witnesses),'finite_checks_not_infinitude_proof':True,'native_sources':{f:hashlib.sha256((M/'python/phonological_requirements'/f).read_bytes()).hexdigest() for f in ['core.py','frag_seq.py','evaluate.py']},'complete_minimizers':records,'witnesses':witnesses}
certificate.write('irrational_selection.json',result)
print(json.dumps({k:v for k,v in result.items() if k not in ['complete_minimizers','witnesses']},indent=2))
