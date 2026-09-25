from pathlib import Path
import datetime, json, sys
from .certificate import write
import numpy as np
from scipy.optimize import minimize
from scipy.special import expit

W=Path(sys.argv[1]).resolve()
rows=json.loads((W/"response_rows.json").read_text())
variant=sys.argv[2] if len(sys.argv)>2 else "all"
if variant=="no_overlap":
    overlap=json.loads((W/"metadata.json").read_text())["overlap"]
    rows=[r for r in rows if r["model_base"] not in overlap]
fitdata=np.load(W/"design.npz")
starts=fitdata["starts"]; lengths=fitdata["lengths"]; groups=fitdata["groups"]
y=np.array([[int(r["accept.faithful"]),int(r["accept.deletion"])] for r in rows])
targets=np.array([[r["faithful_row"],r["deletion_row"]] for r in rows])
ptest=np.array([r["person_test"] for r in rows]);ctest=np.array([r["cluster_test"] for r in rows])
cal=~ptest&~ctest
splits={"calibration":cal,"primary_both":ptest&ctest,
        "participant_only":ptest&~ctest,"cluster_only":~ptest&ctest}
first=np.array([[r["order"]=="TRUE",r["order"]!="TRUE"] for r in rows],float)
trial=np.array([int(r["trialnumber"]) for r in rows],float)
trial=(trial-trial[cal].mean())/74
people=np.array([r["userCode"] for r in rows]);clusters=np.array([r["cluster"] for r in rows])

def calibrate(X,Y,beta_idx=1,offset=None):
    if offset is None:offset=np.zeros(len(Y))
    def objective(v):
        eta=X@v+offset; q=expit(eta)
        return float(np.sum(np.logaddexp(0,eta)-Y*eta)),X.T@(q-Y)
    bounds=[(0,None) if j==beta_idx else (None,None) for j in range(X.shape[1])]
    fit=minimize(objective,np.zeros(X.shape[1]),method="L-BFGS-B",jac=True,bounds=bounds,
                 options={"maxiter":10000,"ftol":1e-15,"gtol":1e-8,"maxls":80})
    grad=fit.jac.copy()
    if beta_idx is not None and fit.x[beta_idx]<1e-8 and grad[beta_idx]>0:grad[beta_idx]=0
    pg=float(np.max(abs(grad)))
    if pg>1e-5:
        fit=minimize(objective,fit.x,method="L-BFGS-B",jac=True,bounds=bounds,
                     options={"maxiter":10000,"ftol":0,"gtol":1e-8,"maxls":100})
        grad=fit.jac.copy()
        if beta_idx is not None and fit.x[beta_idx]<1e-8 and grad[beta_idx]>0:grad[beta_idx]=0
        pg=float(np.max(abs(grad)))
    newton_steps=0
    while pg>=1e-5 and newton_steps<30:
        q=expit(X@fit.x+offset)
        H=X.T@((q*(1-q))[:,None]*X)
        active=np.ones(len(fit.x),bool)
        if beta_idx is not None and fit.x[beta_idx]<1e-8 and fit.jac[beta_idx]>0:active[beta_idx]=False
        step=np.zeros(len(fit.x));step[active]=np.linalg.solve(H[np.ix_(active,active)],fit.jac[active])
        rate=1.
        if beta_idx is not None and step[beta_idx]>0:rate=min(rate,.99*fit.x[beta_idx]/step[beta_idx])
        for _ in range(40):
            candidate=fit.x-rate*step
            obj,g=objective(candidate)
            if obj<=fit.fun+1e-10:break
            rate*=.5
        fit.x=candidate;fit.fun=obj;fit.jac=g
        grad=g.copy()
        if beta_idx is not None and fit.x[beta_idx]<1e-8 and grad[beta_idx]>0:grad[beta_idx]=0
        pg=float(np.max(abs(grad)));newton_steps+=1
    assert pg<1e-5,(fit.message,pg)
    return fit.x,{"coefficients":fit.x.tolist(),"pg":pg,"iterations":int(fit.nit),
                  "message":str(fit.message),"accepted":True,"newton_polish_steps":newton_steps}

def bootstrap_difference(a,b,mask,seed=2026092001):
    diff=(a-b)[mask]
    ps,pi=np.unique(people[mask],return_inverse=True)
    cs,ci=np.unique(clusters[mask],return_inverse=True)
    rng=np.random.default_rng(seed);boot=[]
    for _ in range(2000):
        pm=rng.multinomial(len(ps),np.full(len(ps),1/len(ps)))
        cm=rng.multinomial(len(cs),np.full(len(cs),1/len(cs)))
        wt=pm[pi]*cm[ci]
        if wt.sum():boot.append(float(wt@diff/wt.sum()))
    return {"difference":float(diff.mean()),"interval95":np.quantile(boot,[.025,.975]).tolist(),
            "resamples":len(boot),"participants":len(ps),"clusters":len(cs),
            "scope":"Crossed participant/cluster bootstrap conditional on trained grammar and calibrated response link"}

saved={"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"variant":variant,
       "splits":{k:{"trials":int(v.sum()),"participants":len(set(people[v])),
                     "clusters":len(set(clusters[v]))} for k,v in splits.items()},
       "fits":[],"contrasts":[]}
predictions={}; lossstore={}
for sampling in (["corrected_left","uncorrected_left"] if variant=="left" else ["corrected","uncorrected"]):
    for model in ["retained","current","zero","expanded","sublexical"]:
        lp=np.load(W/f"final_{sampling}_{model}_0.npz")["logprob"]
        logs=lp[targets]
        lognot=np.empty_like(logs)
        for i in range(len(rows)):
            for j in range(2):
                t=targets[i,j];g=groups[t];a=starts[g];b=a+lengths[g]
                rest=[k for k in range(a,b) if k!=t]
                lognot[i,j]=np.logaddexp.reduce(lp[rest])
        for link in ["log_probability","fixed_beta_one","logit_probability"]:
            x=logs-lognot if link=="logit_probability" else logs
            if link=="fixed_beta_one":
                X=np.stack([np.ones_like(x),first,np.repeat(trial[:,None],2,axis=1)],axis=2)
                coeff,detail=calibrate(X[cal].reshape(-1,3),y[cal].ravel(),None,x[cal].ravel())
                eta=X@coeff+x
            else:
                X=np.stack([np.ones_like(x),x,first,np.repeat(trial[:,None],2,axis=1)],axis=2)
                coeff,detail=calibrate(X[cal].reshape(-1,4),y[cal].ravel())
                eta=X@coeff
            q=expit(eta);loss=np.logaddexp(0,eta)-y*eta
            key=f"{sampling}|{model}|{link}";predictions[key]=q;lossstore[key]=loss.sum(axis=1)
            rec={"sampling":sampling,"model":model,"link":link,"calibration":detail,"evaluation":{}}
            for name,mask in splits.items():
                ev={"trials":int(mask.sum()),"sum_binary_logloss_per_trial":float(loss[mask].sum()/mask.sum()),
                    "faithful_logloss":float(loss[mask,0].mean()),"deletion_logloss":float(loss[mask,1].mean()),
                    "faithful_Brier":float(((q[mask,0]-y[mask,0])**2).mean()),
                    "deletion_Brier":float(((q[mask,1]-y[mask,1])**2).mean()),
                    "predicted_rates":q[mask].mean(axis=0).tolist(),"observed_rates":y[mask].mean(axis=0).tolist()}
                rec["evaluation"][name]=ev
            rec["calibration_bins"]=[]
            for alt in [0,1]:
                indices=np.flatnonzero(splits["primary_both"])
                indices=indices[np.argsort(q[indices,alt])]
                for b,ii in enumerate(np.array_split(indices,5)):
                    rec["calibration_bins"].append({"alternative":alt,"bin":b,"n":len(ii),
                        "prediction":float(q[ii,alt].mean()),"observed":float(y[ii,alt].mean())})
            saved["fits"].append(rec)
            print(json.dumps({"sampling":sampling,"model":model,"link":link,
                              "primary":rec["evaluation"]["primary_both"],"calibration":detail}),flush=True)
        discord=y.sum(axis=1)==1
        X=np.c_[logs[:,1]-logs[:,0],first[:,1]-first[:,0]]
        coeff,detail=calibrate(X[cal&discord],y[cal&discord,1],0)
        eta=X@coeff;loss=np.logaddexp(0,eta)-y[:,1]*eta
        saved["fits"].append({"sampling":sampling,"model":model,"link":"paired_discordant",
                             "calibration":detail,"evaluation":{name:{"trials":int((mask&discord).sum()),
                             "logloss":float(loss[mask&discord].mean())} for name,mask in splits.items()}})
        predictions[f"{sampling}|{model}|paired_discordant"]=expit(eta)
        lossstore[f"{sampling}|{model}|paired_discordant"]=loss
    for link in ["log_probability","fixed_beta_one","logit_probability","paired_discordant"]:
        for rival in ["current","zero","expanded","sublexical"]:
            a=lossstore[f"{sampling}|retained|{link}"];b=lossstore[f"{sampling}|{rival}|{link}"]
            mask=splits["primary_both"].copy()
            if link=="paired_discordant":mask&=y.sum(axis=1)==1
            rec=bootstrap_difference(a,b,mask)
            saved["contrasts"].append({"sampling":sampling,"retained_minus_rival":rival,"link":link,**rec})
            print(json.dumps(saved["contrasts"][-1]),flush=True)
suffix="" if variant=="all" else "_"+variant
np.savez_compressed(W/f"response_predictions{suffix}_v1.npz",**predictions)
np.savez_compressed(W/f"response_losses{suffix}_v1.npz",**lossstore)
write(f"response_fits{suffix}_v1.json",saved,W)
print("DONE",flush=True)
