from dataclasses import dataclass
from pathlib import Path
import hashlib
import numpy as np
from scipy.optimize import minimize
from scipy.special import logsumexp
import statistical_protocol_v2 as frozen

FROZEN_SHA='9428d7f030f31f3ac2122806bad36d3cc3641399bec4b5a12ad031d54af977fd'

@dataclass(frozen=True)
class StableGrammarFit(frozen.GrammarFit):
    optimizer: str
    optimization_attempts: tuple[dict,...]

def stable_objective_gradient(theta,features,counts,d,alpha):
    theta=np.asarray(theta,dtype=float)
    costs=np.einsum('ncp,p->nc',features,theta)
    costs[:,2:]+=d[:,None]
    centered=costs-costs.min(axis=1,keepdims=True)
    logp=-centered-logsumexp(-centered,axis=1,keepdims=True)
    totals=counts.sum(axis=1);N=float(totals.sum())
    objective=-float(np.sum(counts*logp))/N+alpha*float(theta@theta)/2
    gradient=np.einsum('ncp,nc->p',features,counts-totals[:,None]*np.exp(logp))/N+alpha*theta
    return objective,gradient

def fit_grammar(model,counts,opposed,d,p_hc_b=None,old_is_back=None,alpha=0.):
    if hashlib.sha256(Path(frozen.__file__).read_bytes()).hexdigest()!=FROZEN_SHA:
        raise RuntimeError('frozen numerical definitions changed')
    counts=np.asarray(counts,dtype=float);opposed=np.asarray(opposed,dtype=bool);d=np.asarray(d,dtype=float)
    old=np.ones(len(opposed),dtype=bool) if old_is_back is None else np.asarray(old_is_back,dtype=bool)
    q=np.full(len(opposed),np.nan) if p_hc_b is None else np.asarray(p_hc_b,dtype=float)
    if counts.shape!=(len(opposed),4) or d.shape!=(len(opposed),) or np.any(counts<0) or counts.sum()<=0 or alpha<0:
        raise ValueError('invalid grammar arrays')
    if np.any(~np.isfinite(counts)) or np.any(~np.isfinite(d)):
        raise ValueError('nonfinite data')
    features=frozen._grammar_feature_tensor(model,opposed,q,old)
    dimension=features.shape[2]
    objective=lambda t:stable_objective_gradient(t,features,counts,d,alpha)
    attempts=[];selected=None
    for method,options in [('L-BFGS-B',{'maxiter':1000,'ftol':1e-13,'gtol':1e-9,'maxls':100}),
                           ('SLSQP',{'maxiter':1000,'ftol':1e-13})]:
        result=minimize(objective,np.full(dimension,.25),jac=True,method=method,
                        bounds=[(0.,None)]*dimension,options=options)
        value,gradient=objective(result.x)
        numeric=frozen.finite_difference_gradient(lambda t:objective(t)[0],result.x)
        pg=float(np.max(abs(frozen.projected_gradient(result.x,gradient))))
        fd_error=float(np.max(abs(numeric-gradient)))
        old_value,old_gradient=frozen.grammar_objective_gradient(result.x,model,counts,opposed,d,q,old,alpha)
        if abs(value-old_value)>1e-9 or np.max(abs(gradient-old_gradient))>1e-9:
            raise RuntimeError('stable/frozen objective or gradient disagreement')
        passed=bool(result.success) and pg<=1e-5 and fd_error<=2e-5 and np.isfinite(value) and np.all(np.isfinite(result.x))
        attempts.append({'optimizer':method,'success':bool(result.success),'status':int(result.status),
            'message':str(result.message),'iterations':int(result.nit),'objective':value,
            'projected_gradient_max':pg,'finite_difference_error':fd_error,'existing_gate_passed':bool(passed)})
        selected=(result,value,gradient,pg,fd_error,method)
        if passed:break
    result,value,gradient,pg,fd_error,method=selected
    t=result.x
    if model=='retention':parameters={'A':float(t[0]+t[1]),'B':float(t[0])}
    elif model=='retention_nonnegative':parameters={'A':float(t[0]),'B':float(t[1])}
    elif model=='current_only':parameters={'C':float(t[0])}
    elif model=='input_surface':parameters={'input':float(t[0]),'surface':float(t[1])}
    elif model=='hu_surface':parameters={'surface':float(t[0]),'HU':float(t[1])}
    elif model=='retention_hu':parameters={'A':float(t[0]+t[1]),'B':float(t[0]),'HU':float(t[2])}
    else:raise ValueError(model)
    return StableGrammarFit(model=model,parameters=parameters,objective=value,regularization_alpha=alpha,
        converged=bool(result.success),iterations=int(result.nit),internal_coordinates=tuple(map(float,t)),
        gradient=tuple(map(float,gradient)),projected_gradient_max_abs=pg,finite_difference_max_abs_error=fd_error,
        optimizer=method,optimization_attempts=tuple(attempts))
