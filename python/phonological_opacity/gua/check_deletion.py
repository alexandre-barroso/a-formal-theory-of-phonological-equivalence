from fractions import Fraction as Q
import json,sys
from phonological_opacity.gua.grammar import GRAMMAR, INPUTS_DELETION, PROBE
from phonological_opacity.gua.model import Model
g=GRAMMAR;w=[20,1,1,2,4,8,8,24,1]
def counts(m,s):
    C,D,G,src=m.read(s);C0,D0,G0,_=m.read(m.origin);out=[]
    for k in range(9):
        row=[0]*6
        for q in range(m.n):
            p=D[k][q] and not G[k][q];b=C[k][q];a=C0[k][q];v=a and D0[k][q] and not G0[k][q]
            z=[p and a,p and not a and b,p and v,p and not v and b,p and b and v,p and b and not v] if 4<=k<=7 else [p and b,False]*3
            row=[x+int(y) for x,y in zip(row,z)]
        out.append(row)
    return out
def coefficients(cs,policy):
    return [[0,0] if k==7 and policy==1 else r[4:6] if k==7 and policy==2 else r[2:4] for k,r in enumerate(cs)]
def score(cs,policy): return sum(v*(8*a+b) for v,(a,b) in zip(w,coefficients(cs,policy)))
def summary(records,fiber):
    out=[]
    for pol in range(3):
        vals=[score(r[9],pol) for r in records];mn=min(vals);wins=[i for i,p in enumerate(vals) if p==mn]
        correct=[i for i in wins if i in fiber];wrong=[i for i in wins if i not in fiber]
        out.append(dict(policy=pol,minimum8=mn,winners=wins,outputs=sorted(set(records[i][3] for i in wins)),
          exclusively_correct=not wrong,correct_minima=correct,wrong_minima=wrong,
          correct_fiber_scores8=[[i,vals[i]] for i in fiber],
          best_wrong8=min(p for i,p in enumerate(vals) if i not in fiber)))
    return out
def main():
    from phonological_opacity.gua.observations import OBSERVATIONS_DELETION
    inputs=INPUTS_DELETION;obs=OBSERVATIONS_DELETION;cases=[]
    for u in inputs:
        m=Model(g,u);records=[]
        for i,co in enumerate(m.states):
            s=m.expand(co);r=m.read(s);cs=counts(m,s)
            records.append([i,list(co),list(s),m.realize(s),m.lexical_view(s),*r,cs,[score(cs,j) for j in range(3)]])
        o=next(x for x in obs if x['id']==u['id']);fiber=[r[0] for r in records if r[3] in o['allowed']]
        result=dict(id=u['id'],start=m.start,fiber=fiber,global_results=summary(records,fiber),records=records)
        cases.append(result);print(u['id'],json.dumps({k:v for k,v in result.items() if k!='records'},ensure_ascii=False),flush=True)
    assert [x['fiber'] for x in cases]==[[1189,1261],[9,117],[159]]
    z=[0,0];M=[z]*9
    def one(k): return [[1,0] if i==k else [0,0] for i in range(9)]
    for pol in [1,2]:
        assert coefficients(cases[2]['records'][159][9],pol)==one(3)
        assert coefficients(cases[2]['records'][3][9],pol)==one(0)
        assert coefficients(cases[1]['records'][161][9],pol)==one(3)
        assert coefficients(cases[1]['records'][117][9],pol)==one(0)
        assert coefficients(cases[1]['records'][9][9],pol)==[[1,0] if k in [0,2,8] else [0,0] for k in range(9)]
    from phonological_opacity.gua import check_selection
    old=check_selection.compute(verbose=False);baseline=[]
    for c in old['cases']:
        rs=c['records'];start=rs[c['start']]
        assert all(not(a and d and not h) for a,d,h in zip(start[5][7],start[6][7],start[7][7]))
        assert all(r[9][7][2:4]==r[9][7][4:6] for r in rs)
        vals=[score(r[9],1) for r in rs];mn=min(vals);wins=[i for i,x in enumerate(vals) if x==mn]
        assert wins==c['fiber'];assert all(r[9][0][2]==0 for r in rs if vals[r[0]]<=28)
        baseline.append(dict(id=c['id'],source='selection reader records',new_calculation='removed-deletion ablation only',
          minimum8=mn,winners=wins,current_identity=True,initial_D_loci=[],max_budget8=160,
          low_budget_states=[i for i,x in enumerate(vals) if x<=28]))
    pr=PROBE;m=Model(g,pr);r0=m.read(m.origin);probe=[]
    assert r0[0][5][0] and r0[1][5][0] and not r0[2][5][0]
    for s in pr['states']:
        C,D,G,_=m.read(s);p=D[5][0] and not G[5][0]
        live=[i for i,x in enumerate(s) if m.ft(x)['present']];nxt=next(i for i in live if i>0)
        probe.append(dict(state=s,nextLive=nxt,context=C[5][0],defined=D[5][0],good=G[5][0],retained8=64*int(p)))
    assert [x['retained8'] for x in probe]==[0,64] and all(x['nextLive']==2 and not x['context'] for x in probe)
    print('PASS complete records of the three deletion products, the deletion ablation and the phrase-domain probe.')
    return 0
if __name__=='__main__': raise SystemExit(main())
