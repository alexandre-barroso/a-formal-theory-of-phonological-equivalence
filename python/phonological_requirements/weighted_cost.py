import itertools,json,random
from . import certificate
def windows(u):
    return [tuple(u[k] if 0<=k<len(u) else None for k in range(i-2,i+3)) for i in range(len(u))]
def delayed(u,flush=True):
    left=(None,None);pending=[];out=[]
    for x in u:
        pending.append(x)
        if len(pending)==3:
            c,d,e=pending;out.append((*left,c,d,e));left=(left[1],c);pending=pending[1:]
    if flush:
        while pending:
            c=pending[0];out.append((*left,c,pending[1] if len(pending)>1 else None,None))
            left=(left[1],c);pending=pending[1:]
    return out
def menu(j,c):return () if j==5 and c==1 else tuple(range(3 if j in (3,4) else 2))
def weight(j,q,w,o):
    return 0 if j==0 else ((q+1)*(w[2]+2)+(o+1)*j+sum((k+1)*(0 if x is None else x+1) for k,x in enumerate(w)))%7
def final(j,q):return 0 if j==0 else (j*(q+1))%4
def brute(j,u):
    ws=windows(u);rows=[]
    for v in itertools.product(*(menu(j,c) for c in u)):
        q=0;cost=0
        for w,o in zip(ws,v):cost+=weight(j,q,w,o);q=o
        rows.append((cost+final(j,q),v))
    return rows
def compute(j,u,pairs=False,cap=True,emit=True,term=True,flush=True):
    layer={(0,0)};offset=0;history=[];K=0 if j==0 else 6
    for w in delayed(u,flush):
        expanded={(o,c+weight(j,q,w,o)) for q,c in layer for o in menu(j,w[2])}
        if not expanded:return None,history
        m=min(c for q,c in expanded)
        if emit:offset+=m
        layer={(q,c-m) for q,c in expanded if not cap or c<=m+K}
        if not pairs:layer={(q,min(c for qq,c in layer if q==qq)) for q in {q for q,c in layer}}
        history.append((offset,tuple(sorted(layer))))
    return offset+min(c+(final(j,q) if term else 0) for q,c in layer),history
def main():
    counts=dict(raw_inputs=0,candidate_scores=0,feasible_inputs=0,infeasible_inputs=0,vector_pair_matches=0,long_inputs=0)
    tables=[];mutants={}
    for j in range(6):
     for n in range(6):
      for u in itertools.product((0,1),repeat=n):
        assert delayed(u)==windows(u)
        rows=brute(j,u);target=min((s for s,_ in rows),default=None)
        value,trace=compute(j,u);pair,ptrace=compute(j,u,pairs=True)
        assert value==target==pair,(j,u,target,value,pair)
        for (o,V),(p,W) in zip(trace,ptrace):
            assert o==p and dict(V)=={q:min(c for qq,c in W if q==qq) for q,c in W}
            counts['vector_pair_matches']+=1
        counts['raw_inputs']+=1;counts['candidate_scores']+=len(rows)
        counts['feasible_inputs' if rows else 'infeasible_inputs']+=1
        tables.append([j,list(u),target])
        for name,kw in [('omit_offsets',{'emit':False}),('omit_terminal',{'term':False}),('omit_reference_flush',{'flush':False})]:
            got,_=compute(j,u,**kw)
            if got!=target and name not in mutants:mutants[name]={'grammar':j,'input':u,'true':target,'mutated':got}
    rng=random.Random(202609200137)
    for j in range(6):
     for n in (7,13,40,120):
      for _ in range(3):
        u=tuple(rng.randrange(2) for _ in range(n))
        assert delayed(u)==windows(u)
        assert compute(j,u)[0]==compute(j,u,cap=False)[0]
        counts['long_inputs']+=1
    assert counts['raw_inputs']==378 and counts['infeasible_inputs']>0 and len(mutants)==3
    out={'counts':counts,'seed':202609200137,'mutants':mutants,'tables':tables,'scope':'Independent exhaustive raw-input costs; native local-score correspondence proved in Application/Regularity. K=6 derives from forgetting the source state after one output and transition range0..6, final range0..3. K=0 for all-zero grammar.'}
    certificate.write('weighted_cost.json',out)
    print(json.dumps({k:v for k,v in out.items() if k!='tables'}))

if __name__ == "__main__":
    main()
