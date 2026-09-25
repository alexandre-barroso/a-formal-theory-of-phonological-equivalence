from pathlib import Path
import datetime, json, sys, time
from .certificate import write
import numpy as np
from scipy.sparse import csr_matrix, hstack, load_npz
from scipy.optimize import minimize

W=Path(sys.argv[1]).resolve()
z=np.load(W/"design.npz")
O,N,F=z["right_old"],z["right_new"],z["faithfulness"]
starts=z["starts"]; groups=z["groups"]; nlex=int(z["nlex"]); nglex=int(z["nglex"])
st=starts[:nglex]; gr=groups[:nlex]; yc=z["ycounts"][:nlex]; gc=z["groupcounts"][:nglex]
val=z["lexvalidation"][:nglex]
op=(F[:,0]>0).astype(int)*2+(F[:,1:].sum(axis=1)>0).astype(int)
source=hstack([csr_matrix(z['base_marks']*(op==j)[:,None]) for j in range(4)]+[csr_matrix(z['current']*(op==j)[:,None]) for j in range(4)]+[csr_matrix(F),csr_matrix(np.eye(4)[op,1:])],format='csr')
offset_mode=sys.argv[2] if len(sys.argv)>2 else "corrected"
if offset_mode not in ['corrected','uncorrected','corrected_left','uncorrected_left']:raise ValueError(offset_mode)
if offset_mode.endswith("_left"):
    O=z['left_old'].astype(float)
    N=z['left_new'].astype(float)
ofs=np.where(F[:nlex,0]>0,0,np.log(600/18661)) if offset_mode.startswith("corrected") else np.zeros(nlex)
outpath=W/f"lexical_fits_{offset_mode}_v1.json"
saved={"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"sampling":offset_mode,
       "grid":[],"final":[],"gradient_checks":[]}

def matrix(kind,lam):
    if kind=="retained":X=csr_matrix(np.c_[O+lam*N,F]);nc=X.shape[1]
    elif kind=="ordinary":X=csr_matrix(np.c_[z["current"],F]);nc=X.shape[1]
    elif kind=="expanded":X=csr_matrix(np.c_[O,N,F]);nc=X.shape[1]
    elif kind=="sublexical":X=source;nc=X.shape[1]-3
    else:raise ValueError(kind)
    X=(X-X[starts[groups]]).tocsr()
    keep=np.flatnonzero(np.asarray(abs(X[:nlex]).sum(axis=0)).ravel()>0)
    return X[:,keep].tocsr(),keep,np.array([k<nc for k in keep])

def loglaw(X,w,off,starts,groups):
    eta=-(X@w)+off
    mx=np.maximum.reduceat(eta,starts)
    exp=np.exp(eta-mx[groups])
    sums=np.add.reduceat(exp,starts)
    lp=eta-mx[groups]-np.log(sums[groups])
    return lp,np.exp(lp)

def fitting(X,nonnegative,rho,train,start=None):
    XX=X[:nlex];weights=gc*train; targets=yc*train[gr]
    def fun(w):
        lp,p=loglaw(XX,w,ofs,st,gr)
        return -targets@lp+rho/2*(w@w),np.asarray(XX.T@(targets-weights[gr]*p)).ravel()+rho*w
    if start is None:start=np.zeros(X.shape[1])
    bounds=[(0,None) if b else (None,None) for b in nonnegative]
    fit=minimize(fun,start,method="L-BFGS-B",jac=True,bounds=bounds,
                 options={"maxiter":10000,"ftol":1e-15,"gtol":1e-8,"maxls":60,"maxcor":30})
    def pg(fit):
        g=fit.jac.copy();g[nonnegative & (fit.x<1e-8) & (g>0)]=0
        return float(np.max(abs(g)))
    attempts=[{"success":bool(fit.success),"message":str(fit.message),"iterations":int(fit.nit),"pg":pg(fit)}]
    if pg(fit)>1e-5:
        fit=minimize(fun,fit.x,method="L-BFGS-B",jac=True,bounds=bounds,
                     options={"maxiter":10000,"ftol":0,"gtol":1e-7,"maxls":100,"maxcor":50})
        attempts.append({"success":bool(fit.success),"message":str(fit.message),"iterations":int(fit.nit),"pg":pg(fit)})
    fit.pg=pg(fit);fit.attempts=attempts
    return fit,fun

for kind in (["retained","expanded","sublexical","ordinary"] if offset_mode.endswith("_left") else ["retained","expanded","sublexical"]):
    lambdas=[0.,.1,.25,.5,.75,1.] if kind=="retained" else [None]
    for lam in lambdas:
        X,keep,nonnegative=matrix(kind,lam)
        for rho in [.1,1.,10.]:
            begin=time.monotonic()
            fit,fun=fitting(X,nonnegative,rho,~val)
            lp,_=loglaw(X[:nlex],fit.x,ofs,st,gr)
            record={"model":kind,"lambda":lam,"rho":rho,"parameters":len(keep),
                    "validation_nll":float(-np.dot(yc*val[gr],lp)),
                    "training_nll":float(-np.dot(yc*(~val)[gr],lp)),
                    "penalized_objective":float(fit.fun),"projected_gradient":fit.pg,
                    "accepted":fit.pg<=1e-5,"attempts":fit.attempts,
                    "seconds":time.monotonic()-begin}
            v=np.full(len(keep),.13);v[~nonnegative]=-.17
            base,gradient=fun(v)
            errors=[]
            for j in np.unique(np.linspace(0,len(v)-1,min(12,len(v)),dtype=int)):
                lo=v.copy();hi=v.copy();lo[j]-=1e-5;hi[j]+=1e-5
                errors.append(abs((fun(hi)[0]-fun(lo)[0])/2e-5-gradient[j]))
            assert max(errors)<1e-5,(kind,lam,rho,errors)
            record["max_fd_error"]=max(errors)
            saved["grid"].append(record)
            write(outpath.name,saved,outpath.parent)
            np.savez_compressed(W/f"grid_{offset_mode}_{kind}_{lam}_{rho}.npz",
                                coefficients=fit.x,keep=keep)
            print(json.dumps(record),flush=True)

for label,kind,lamfixed in [("retained","retained",None),("current","ordinary" if offset_mode.endswith("_left") else "retained",None if offset_mode.endswith("_left") else 1.),
                           ("zero","retained",0.),("expanded","expanded",None),
                           ("sublexical","sublexical",None)]:
    eligible=[r for r in saved["grid"] if r["model"]==kind and r["accepted"] and
              (lamfixed is None or r["lambda"]==lamfixed)]
    if not eligible:
        saved["final"].append({"model":label,"accepted":False,"reason":"No converged tuning fit"})
        continue
    best=min(eligible,key=lambda r:(round(r["validation_nll"],8),-r["rho"],
                                   -(r["lambda"] if r["lambda"] is not None else 0)))
    lam,rho=best["lambda"],best["rho"]
    X,keep,nonnegative=matrix(kind,lam)
    coefficients=[];records=[]
    for seed in [0,2026092002]:
        init=np.zeros(len(keep)) if seed==0 else np.random.default_rng(seed).uniform(.01,.3,len(keep))
        begin=time.monotonic()
        fit,fun=fitting(X,nonnegative,rho,np.ones(nglex,bool),init)
        lp,_=loglaw(X,fit.x,np.zeros(len(O)),starts,groups)
        rec={"model":label,"family":kind,"lambda":lam,"rho":rho,"seed":seed,
             "parameters":len(keep),"projected_gradient":fit.pg,"accepted":fit.pg<=1e-5,
             "objective":float(fit.fun),"attempts":fit.attempts,"seconds":time.monotonic()-begin}
        records.append(rec);coefficients.append(fit.x)
        np.savez_compressed(W/f"final_{offset_mode}_{label}_{seed}.npz",
                            coefficients=fit.x,keep=keep,logprob=lp)
        print(json.dumps(rec),flush=True)
    records[0]["other_start_max_prediction_difference"]=float(np.max(abs(
        loglaw(X,coefficients[0],np.zeros(len(O)),starts,groups)[0]-
        loglaw(X,coefficients[1],np.zeros(len(O)),starts,groups)[0])))
    saved["final"].extend(records)
    write(outpath.name,saved,outpath.parent)
print("DONE",offset_mode,flush=True)
