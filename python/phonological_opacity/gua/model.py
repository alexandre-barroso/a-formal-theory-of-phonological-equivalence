from itertools import product

class Model:
 def __init__(self,g,c):
  self.g=g;self.c=c;self.slots=c['slots'];self.focal=c['focal'];self.alpha=g['alphabet'];self.origin=tuple(x['phone'] for x in self.slots)
  self.inv=g['inventory'];self.words=[x['word'] for x in self.slots];self.phrases=c['phrases'];self.types=g['types'];self.n=len(self.origin)
  self.origft=[self.ft(p) for p in self.origin]
  self.states=list(product(range(len(self.alpha)),repeat=len(self.focal)))
  self.powers=[len(self.alpha)**i for i in reversed(range(len(self.focal)))]
  self.prior=self.read(self.origin)[0]
  self.start=sum(self.alpha.index(self.origin[q])*p for q,p in zip(self.focal,self.powers))
 def ft(self,p): return self.inv.get(p,dict(nuclear=False,present=True,atr=None,quality=None,high=False))
 def expand(self,coords):
  s=list(self.origin)
  for q,k in zip(self.focal,coords):s[q]=self.alpha[k]
  return tuple(s)
 def read(self,s):
  fs=[self.ft(p) for p in s];live=[q for q in range(self.n) if fs[q]['present']];nuc=[q for q in live if fs[q]['nuclear']]
  nxt=dict(zip(live,live[1:]));prev=dict(zip(live[1:],live));last={}
  for q in nuc:last[self.words[q]]=q
  C=[[False]*self.n for _ in self.types];D=[[True]*self.n for _ in self.types];G=[[True]*self.n for _ in self.types];sources=[-1]*self.n
  for q in range(self.n):
   f=fs[q];r=self.origft[q];w=self.words[q];n=nxt.get(q);v=prev.get(q)
   for k in range(4):C[k][q]=True
   G[0][q]=f['present'];D[1][q]=f['nuclear'] and r['nuclear'];G[1][q]=f['atr']==r['atr']
   D[2][q]=f['present'] and f['quality'] is not None and r['quality'] is not None;G[2][q]=f['quality']==r['quality']
   D[3][q]=f['present'];G[3][q]=f['nuclear']==r['nuclear']
   src=next((j for j in nuc if j>q and self.words[j]>w and self.phrases[self.words[j]]==self.phrases[w]),None)
   sources[q]=-1 if src is None else src
   C[4][q]=f['nuclear'] and last.get(w)==q and src is not None and fs[src]['atr'] is True
   D[4][q]=f['nuclear'];G[4][q]=f['atr'] is True
   cross=n is not None and self.words[n]==w+1 and self.phrases[self.words[n]]==self.phrases[w]
   C[5][q]=f['nuclear'] and not f['high'] and cross and fs[n]['nuclear'] and not fs[n]['high']
   G[5][q]=not f['present'] or (n is not None and s[q]==s[n])
   neighbor=any(j is not None and abs(self.words[j]-w)==1 and self.phrases[self.words[j]]==self.phrases[w] and fs[j]['nuclear'] and not fs[j]['high'] for j in [v,n])
   C[6][q]=f['nuclear'] and f['high'] and neighbor;G[6][q]=not f['nuclear']
   C[7][q]=f['nuclear'] and f['high'] and v is not None and self.words[v]+1==w and self.phrases[self.words[v]]==self.phrases[w] and fs[v]['nuclear'] and fs[v]['high'];G[7][q]=not f['present']
   C[8][q]=r['nuclear'] and (q==0 or self.words[q-1]!=w)
   D[8][q]=f['present'] and f['quality'] is not None
   G[8][q]=f['quality']==r['quality'] and (not f['nuclear'] or f['atr']==r['atr'])
  return C,D,G,sources
 def coefficients(self,s):
  C,D,G,src=self.read(s);out=[]
  for k in range(len(self.types)):
   pending=[D[k][q] and not G[k][q] for q in range(self.n)]
   out.append([sum(p and a for p,a in zip(pending,self.prior[k])),sum(p and not a and b for p,a,b in zip(pending,self.prior[k],C[k])),sum(p and b for p,b in zip(pending,C[k]))])
  return out
 def pressure(self,cs,mode):
  return sum(w*(4*cur if mode=='current' else 4*old+(4 if mode=='lambda1' else 1)*new) for w,(old,new,cur) in zip(self.g['weights'],cs))
 def edges(self,i):
  coords=self.states[i]
  return [i+(v-old)*power for old,power in zip(coords,self.powers) for v in range(len(self.alpha)) if v!=old]
 def realize(self,s):
  return ''.join(p for p in s if p!='∅')
 def lexical_view(self,s):return [''.join(p for q,p in enumerate(s) if self.words[q]==w and p!='∅') for w in range(len(self.phrases))]

def choice(row):
 m=min(row)
 return [0] if row[0]==m else [j for j,p in enumerate(row) if p==m]

def paths(start,rows,edges):
 out=[]
 def visit(i,path):
  cs=choice(rows[i])
  if cs==[0]:out.append(path);return
  for j in cs:
   t=edges[i][j-1]
   assert t not in path and rows[t][0]<rows[i][0]
   visit(t,path+[t])
 visit(start,[start]);return out
