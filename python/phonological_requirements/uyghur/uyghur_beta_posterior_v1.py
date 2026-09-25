from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
import math
import numpy as np
from scipy.special import betaln, gammaln, logsumexp, roots_jacobi

@dataclass(frozen=True)
class FitGate:
    passed: bool
    reasons: tuple[str,...]

@dataclass(frozen=True)
class BetaPosteriorFit:
    alpha: float
    beta: float
    mu_mean: float
    rho_mean: float
    mu_sd: float
    rho_sd: float
    rho_prior: str
    log_evidence: float
    informative_roots: int
    zero_total_roots: int
    quadrature_order: int
    maximum_mean_change: float
    maximum_shape_relative_change: float
    converged: bool
    history: tuple[dict,...]
    estimation: str = 'POSTERIOR_MEAN_MU_RHO_WITH_DECLARED_BETA_PLUGIN'

@lru_cache(maxsize=32)
def beta_rule(order, a, b):
    x,w=roots_jacobi(order,b-1,a-1)
    values=(x+1)/2
    weights=w/w.sum()
    assert np.all((values>0)&(values<1)) and np.all(weights>0)
    values.flags.writeable=False;weights.flags.writeable=False
    return values,weights

def posterior_grid(successes,totals,rho_prior,order):
    k,n=np.asarray(successes,dtype=float),np.asarray(totals,dtype=float)
    if k.shape!=n.shape or k.ndim!=1 or not len(k) or np.any(~np.isfinite(k)) or np.any(~np.isfinite(n)):
        raise ValueError('invalid beta-binomial arrays')
    if np.any(k<0) or np.any(n<k) or np.any(k!=np.floor(k)) or np.any(n!=np.floor(n)):
        raise ValueError('nonnegative integer counts with k<=n required')
    if rho_prior not in {'uniform','beta_half_half'}:raise ValueError('unknown fixed rho prior')
    mu,mu_weights=beta_rule(order,.5,.5)
    shape=1. if rho_prior=='uniform' else .5
    rho,rho_weights=beta_rule(order,shape,shape)
    c=(1-rho)/rho
    aa=mu[:,None]*c[None,:];bb=(1-mu[:,None])*c[None,:]
    baseline=betaln(aa,bb)
    ll=np.zeros_like(aa)
    grouped=Counter((int(y),int(t)) for y,t in zip(k,n) if t>0)
    for (y,t),multiplicity in grouped.items():
        if t==1:
            term=np.log(mu if y else 1-mu)[:,None]
        else:
            term=betaln(y+aa,t-y+bb)-baseline+gammaln(t+1)-gammaln(y+1)-gammaln(t-y+1)
        ll+=multiplicity*term
    lw=ll+np.log(mu_weights)[:,None]+np.log(rho_weights)[None,:]
    logz=float(logsumexp(lw));mass=np.exp(lw-logz)
    marginal_mu=mass.sum(axis=1);marginal_rho=mass.sum(axis=0)
    m=float(marginal_mu@mu);r=float(marginal_rho@rho)
    vm=float(marginal_mu@((mu-m)**2));vr=float(marginal_rho@((rho-r)**2))
    concentration=(1-r)/r
    result={'order':order,'mu_mean':m,'rho_mean':r,'mu_sd':math.sqrt(vm),'rho_sd':math.sqrt(vr),
            'alpha':m*concentration,'beta':(1-m)*concentration,'log_evidence':logz}
    if not all(math.isfinite(x) for x in result.values()):raise RuntimeError('nonfinite quadrature result')
    return result

def fit_beta_binomial_posterior(successes,totals,rho_prior='uniform'):
    history=[];previous=None;mean_change=shape_change=math.inf;converged=False
    for order in (32,64,128,256,512,1024):
        result=posterior_grid(successes,totals,rho_prior,order)
        history.append(result)
        if previous is not None:
            mean_change=max(abs(result[k]-previous[k]) for k in ('mu_mean','rho_mean'))
            shape_change=max(abs(result[k]-previous[k])/max(abs(result[k]),1e-15) for k in ('alpha','beta'))
            if mean_change<=1e-7 and shape_change<=1e-4 and abs(result['log_evidence']-previous['log_evidence'])<=1e-5:
                converged=True;break
        previous=result
    n=np.asarray(totals)
    return BetaPosteriorFit(alpha=result['alpha'],beta=result['beta'],mu_mean=result['mu_mean'],rho_mean=result['rho_mean'],
        mu_sd=result['mu_sd'],rho_sd=result['rho_sd'],rho_prior=rho_prior,log_evidence=result['log_evidence'],
        informative_roots=int(np.sum(n>0)),zero_total_roots=int(np.sum(n==0)),quadrature_order=order,
        maximum_mean_change=mean_change,maximum_shape_relative_change=shape_change,converged=converged,history=tuple(history))

def beta_binomial_posterior_gate(fit):
    reasons=[]
    if not fit.converged:reasons.append('quadrature_refinement_not_converged')
    if not all(math.isfinite(v) for v in (fit.alpha,fit.beta,fit.mu_mean,fit.rho_mean,fit.log_evidence)):
        reasons.append('nonfinite_posterior_summary')
    if not (fit.alpha>0 and fit.beta>0 and 0<fit.mu_mean<1 and 0<fit.rho_mean<1):
        reasons.append('invalid_interior_posterior_summary')
    if fit.maximum_mean_change>1e-7 or fit.maximum_shape_relative_change>1e-4:
        reasons.append('quadrature_error_above_tolerance')
    return FitGate(passed=not reasons,reasons=tuple(reasons))
