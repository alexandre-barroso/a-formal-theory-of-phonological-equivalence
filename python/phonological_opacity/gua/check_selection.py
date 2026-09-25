import json,sys
from phonological_opacity.gua.grammar import GRAMMAR, INPUTS_SELECTION
from phonological_opacity.gua.model import Model
g=GRAMMAR
inputs=INPUTS_SELECTION
weights=[20,1,1,2,4,8,8,24,1]
def counts(m,s):
    C,D,G,src=m.read(s); C0,D0,G0,_=m.read(m.origin)
    out=[]
    for k in range(9):
        row=[0]*6
        for q in range(m.n):
            p=D[k][q] and not G[k][q]; b=C[k][q]
            if k in [4,5,6,7]:
                a=C0[k][q]; v=a and D0[k][q] and not G0[k][q]
                inc=[p and a,p and not a and b,p and v,p and not v and b,p and b and v,p and b and not v]
            else:
                v=p and b; inc=[v,False,v,False,v,False]
            row=[x+int(y) for x,y in zip(row,inc)]
        out.append(row)
    return out
def scores(cs):
    return [sum(w*(8*r[2*j]+r[2*j+1]) for w,r in zip(weights,cs)) for j in range(3)]
def compute(verbose=True):
    from phonological_opacity.gua.observations import OBSERVATIONS_SELECTION as observations
    cases=[]; total_edges=0
    for u in inputs:
        m=Model(g,u);records=[]
        for i,co in enumerate(m.states):
            s=m.expand(co); r=m.read(s); cs=counts(m,s); ed=m.edges(i)
            assert len(ed)==12*len(m.focal) and len(set(ed))==len(ed)
            assert all(0<=t<len(m.states) and sum(a!=b for a,b in zip(co,m.states[t]))==1 for t in ed)
            records.append([i,list(co),list(s),m.realize(s),m.lexical_view(s),*r,cs,scores(cs),ed])
        ob=next(x for x in observations if x['id']==u['id'])
        fiber=[r[0] for r in records if r[3] in ob['allowed']]
        global_results=[]
        for j in range(3):
            ps=[r[10][j] for r in records]; v=min(ps); wins=[i for i,p in enumerate(ps) if p==v]
            wrong=[p for i,p in enumerate(ps) if i not in fiber]
            global_results.append(dict(minimum8=v,winners=wins,correct=wins==fiber,wrong_margin8=min(wrong)-min(ps[i] for i in fiber)))
        ps=[r[10][2] for r in records]; pending=[m.start]; selected={}; terminals=[]
        while pending:
            i=pending.pop()
            if i in selected:continue
            es=records[i][11]; v=min(ps[t]+8 for t in es)
            ts=[] if ps[i]<=v else [t for t in es if ps[t]+8==v]
            selected[i]=ts
            if not ts:terminals.append(i)
            for t in ts: assert ps[t]+8<ps[i]
            pending.extend(ts)
        local=dict(cost8=8,selected=[[i,selected[i]] for i in sorted(selected)],terminals=sorted(terminals),correct=sorted(terminals)==fiber)
        cases.append(dict(id=u['id'],start=m.start,fiber=fiber,global_results=global_results,local_cm=local,records=[r[:12] for r in records]))
        total_edges+=sum(len(r[11]) for r in records)
        if verbose: print(u['id'],'states',len(records),'fiber',fiber,'global',global_results,'local',local,flush=True)
    return dict(weights=weights,lambda_num=1,lambda_den=8,states=sum(len(c['records']) for c in cases),edges=total_edges,cases=cases)
def main():
    result=compute()
    cases=result['cases']; total_edges=result['edges']
    assert sum(len(c['records']) for c in cases)==6929 and total_edges==245388
    a=cases[0]; goal=a['records'][774]; rival=a['records'][605]
    assert a['fiber']==[774] and goal[3]=='ahetɔɔkpʊkɔ' and rival[3]=='ahɛtɔɔkpʊkɔ'
    assert all(goal[9][k][4:]==[0,0] and rival[9][k][4:]==[0,0] for k in [4,5,6,7])
    assert [goal[9][k][4]-rival[9][k][4] for k in [0,1,2,3,8]]==[0,1,0,0,0]
    assert a['start']==566 and 605 in a['records'][566][11] and 774 not in a['records'][566][11]
    assert 774 not in dict(a['local_cm']['selected'])
    print('PASS complete records of the five selection products and the current-markedness identities of G34a.')
    return 0
if __name__=='__main__': raise SystemExit(main())
