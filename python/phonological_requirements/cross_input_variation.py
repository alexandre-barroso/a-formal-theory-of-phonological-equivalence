from pathlib import Path
from fractions import Fraction
from itertools import product
import json, hashlib

from . import certificate

def windows(word):
    return [tuple(word[j]+1 if 0 <= j < len(word) else 0 for j in range(i-2,i+3)) for i in range(len(word))]

def menu(model, x):
    if model in (0,3): return (None,0,1)
    if x == 0: return (0,)
    if x == 1: return (None,0,1)
    return () if model == 2 else (None,)

def descriptor(w,o): return sum(a*b for a,b in zip(w,(1,2,3,5,7))) + 13*(o+1)
def deletion(model,w): return 0 if model == 3 else (sum(w)+model+3)%21
def point(model,c,left2,left1,right1,right2):
    return 0 if model == 3 or c is None else (c+11*(left2 or 0)+17*(left1 or 0)+19*(right1 or 0)+23*(right2 or 0)+model)%21

def direct(model, word, output, mutate=None):
    ws=windows(word)
    if mutate == 'no_reference': ws=[(0,0,w[2],0,0) for w in ws]
    zs=[descriptor(w,o) for w,o in zip(ws,output) if o is not None]
    deleted=sum(deletion(model,w) for w,o in zip(ws,output) if o is None)
    if mutate == 'no_deletion': deleted=0
    charges=[]
    for i,c in enumerate(zs):
        neighbors=[zs[j] if 0 <= j < len(zs) else None for j in (i-2,i-1,i+1,i+2)]
        charges.append(point(model,c,*neighbors))
    return deleted+sum(charges)

def delayed(model,word,output,flush=True):
    q=[None]*4; cost=0; traces=[]
    for w,o in zip(windows(word),output):
        if o is None: cost+=deletion(model,w)
        else:
            z=descriptor(w,o);cost+=point(model,q[2],q[0],q[1],q[3],z);q=q[1:]+[z]
        traces.append(cost)
    if flush:
        for z in (None,None):cost+=point(model,q[2],q[0],q[1],q[3],z);q=q[1:]+[z]
    return cost,traces

def lcp(a,b):
    n=0
    for x,y in zip(a,b):
        if x!=y:break
        n+=1
    return n

def encode(output):return [(-1 if x is None else x) for x in output]

def main():
    short=[w for n in range(5) for w in product(range(3),repeat=n)]
    longer=[(0,)*(n-3)+(1,2,1) for n in (7,19,43,120)]
    longer += [(0,)*(n-2)+(2,1) for n in (7,19,43,120)]
    counts={'candidate_scores':0,'short_pair_bounds':0,'long_pair_bounds':0,'spliced_candidates':0,'reference_prefixes':0,'infeasible':0,'all_tied_candidates':0}
    mutants={'no_reference':False,'no_deletion':False,'no_terminal_flush':False,'first_winner_only':False,'no_boundary_constant':False}
    rows=[]
    for model in range(4):
        laws={}
        for word in short+longer:
            outputs=list(product(*(menu(model,x) for x in word))) if len(word)<7 or model in (1,2) else []
            if len(word)>=7 and model in (0,3):continue
            scores=[direct(model,word,o) for o in outputs]
            for o,s in zip(outputs,scores):
                assert delayed(model,word,o)[0]==s
                counts['candidate_scores']+=1
                for m in ('no_reference','no_deletion'):mutants[m] |= direct(model,word,o,m)!=s
                mutants['no_terminal_flush'] |= delayed(model,word,o,False)[0]!=s
            if not outputs:
                counts['infeasible']+=1;laws[word]=None
                rows.append({'model':model,'input':list(word),'minimum':None,'winners':[],'scores':[]});continue
            least=min(scores);wins=[o for o,s in zip(outputs,scores) if s==least]
            mutants['first_winner_only'] |= len(wins)>1
            if model==3:assert len(wins)==len(outputs);counts['all_tied_candidates']+=len(wins)
            laws[word]=(least,wins)
            rows.append({'model':model,'input':list(word),'minimum':least,'winners':[encode(o) for o in wins],'scores':scores})
        for u,lu in laws.items():
            if lu is None:continue
            for v,lv in laws.items():
                if lv is None:continue
                k=lcp(u,v);n=max(k-2,0);C=0 if model==3 else 20
                assert windows(u)[:n]==windows(v)[:n];counts['reference_prefixes']+=1
                assert abs(Fraction(lu[0]-lv[0],7)) <= Fraction(C,7)*(4+len(u)+len(v)-2*k)
                counts['short_pair_bounds' if max(len(u),len(v))<7 else 'long_pair_bounds']+=1
                ox,oy=lu[1][0],lv[1][0];spliced=ox[:n]+oy[n:]
                assert all(o in menu(model,x) for x,o in zip(v,spliced)) and len(spliced)==len(v)
                assert direct(model,v,spliced) <= lu[0]+C*(4+len(v)-k)
                counts['spliced_candidates']+=1
    u=(0,)*5;v=u+(1,)
    boundary_score=lambda w:sum(20 for a in windows(w) if 2 in a[3:])
    assert boundary_score(v)-boundary_score(u)==40 > 20*(len(v)-len(u))
    mutants['no_boundary_constant']=True
    assert all(mutants.values())
    result={'status':'PASS','scope':'Finite exact tests, not the universal proof or attested observations','counts':counts,'mutants_detected':mutants,'tables':rows}
    out=certificate.write('cross_input_variation.json',result)
    print(json.dumps({'status':'PASS','counts':counts,'mutants':mutants,'rows':len(rows),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))

if __name__=='__main__':main()
