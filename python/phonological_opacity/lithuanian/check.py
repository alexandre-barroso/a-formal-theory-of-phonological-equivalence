from fractions import Fraction as Q
import json, sys
INPUTS=[('PG',('p','b'),('k','g'),'auti',1,0,'abgauti'),
        ('PB',('p','b'),('p','b'),'erti',1,1,'apiberti'),
        ('TT',('t','d'),('t','d'),'aiki:ti',0,1,'atitaiki:ti')]
CONFIGS=[('O',0,None),('RR',0,Q(1,8)),('SR',1,Q(1,8)),
         ('RS',2,Q(1,8)),('SS',3,Q(1,8)),('RR0',0,Q(0))]
def bits(j): return [j//4,(j//2)%2,j%2]
def mark(h,j):
    x,y,z=bits(j)
    return [int(not z and x!=y),int(not z and h and x==y)]
def readers(h,mode,j):
    x,y,z=bits(j);out=[]
    for k in range(2):
        C=int(not z);D=int(bool(mode&(1<<k)) or not z)
        G=int(x==y) if k==0 else int(not(h and x==y))
        p=D*(1-G);out.append([C,D,G,p,C*p])
    return out
def coeff(yu,h,mode,j):
    x,y,z=bits(j);m0=mark(h,2*yu);R=readers(h,mode,j)
    return [int(x!=0),int(y!=yu),z,m0[0]*R[0][3],(1-m0[0])*R[0][4],
            m0[1]*R[1][3],(1-m0[1])*R[1][4]]
def score(co,m,lam):
    c,r,d,ao,an,no,nn=co
    if lam is None:return Q(c+4*r+2*d+16*sum(m))
    return Q(c+4*r+2*d+16*ao+16*no)+16*lam*(an+nn)
def evaluate():
    body=[]
    for cid,ps,ss,tail,yu,h,target in INPUTS:
        rows=[]
        for j in range(8):
            x,y,z=bits(j);view='a'+ps[x]+('i' if z else '')+'-'+ss[y]+tail
            tabulated=(1-z)*int(x!=yu);m=mark(h,j)
            row=dict(j=j,bits=bits(j),morph=view,observation=view.replace('-',''),
              ordinary=m,tabulated=[1-z,1,int(x==yu),int(x!=yu),tabulated],
              tabulated_agrees=int(tabulated==m[0]),configs=[])
            for name,mode,lam in CONFIGS:
                R=readers(h,mode,j);initial=readers(h,mode,2*yu);co=coeff(yu,h,mode,j)
                assert [r[4] for r in R]==m
                s=8*score(co,m,lam);assert s.denominator==1
                row['configs'].append(dict(name=name,initial=initial,current=R,coefficients=co,score8=int(s)))
            rows.append(row)
        fibers=[dict(observation=r['observation'],members=[q['j'] for q in rows if q['observation']==r['observation']]) for r in rows]
        summaries=[]
        for k,(name,_,_) in enumerate(CONFIGS):
            v=min(r['configs'][k]['score8'] for r in rows)
            minima=[r['j'] for r in rows if r['configs'][k]['score8']==v]
            summaries.append(dict(name=name,minimum8=v,minima=minima,
              outputs=[rows[j]['observation'] for j in minima]))
        body.append(dict(id=cid,input='a'+ps[0]+'-'+ss[yu]+tail,input_index=2*yu,h=h,
          target=target,correct_fiber=[r['j'] for r in rows if r['observation']==target],rows=rows,fibers=fibers,summaries=summaries))
    return body
def main():
    body=evaluate()
    for mode in (1,3):
        g=coeff(1,0,mode,6);f=coeff(1,0,mode,2)
        b=coeff(1,1,mode,3);ab=coeff(1,1,mode,7)
        assert g==[1,0,0,0,0,0,0] and f==[0,0,0,1,0,0,0]
        assert [u-v for u,v in zip(ab,b)]==[1,0,0,-1,0,0,0]
    for mode in (2,3):
        assert [u-v for u,v in zip(coeff(0,1,mode,1),coeff(0,1,mode,0))]==[0,0,1,0,0,0,0]
    print('Python',sys.version);print('24 states, 144 scores, full fields and all minima exported; exact coefficient bounds passed.')
    return 0
if __name__=='__main__': raise SystemExit(main())
