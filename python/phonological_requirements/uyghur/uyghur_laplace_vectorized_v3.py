import math
import numpy as np
from scipy.optimize import minimize
from scipy.special import expit, gammaln

def mode_state(eta, y, n, sigma):
    eta,y,n=map(lambda z:np.asarray(z,dtype=float),(eta,y,n))
    if eta.shape!=y.shape or y.shape!=n.shape or sigma<=0:
        raise ValueError('invalid one-row-per-root dimensions')
    invvar=1/(sigma*sigma)
    b=np.zeros_like(y);u=eta.copy();c=np.zeros_like(y)
    done=np.zeros_like(y,dtype=bool);maxiteration=0
    for coordinate in ('random_effect','conditional_predictor'):
        if coordinate=='random_effect':
            lower=(y-n)/invvar;upper=y/invvar;point=np.clip(b,lower,upper)
        else:
            lower=eta+(y-n)/invvar;upper=eta+y/invvar;point=np.clip(u,lower,upper)
        for iteration in range(1,201):
            bi=point if coordinate=='random_effect' else point-eta
            ui=eta+point if coordinate=='random_effect' else point
            p=expit(ui);pm=expit(-ui);ci=n*p*pm+invvar
            score=y*pm-(n-y)*p-bi*invvar
            active=~done
            b=np.where(active,bi,b);u=np.where(active,ui,u);c=np.where(active,ci,c)
            newly=(np.abs(score)<=1e-13*np.maximum(1,n)) & (np.abs(score)/ci<=1e-10)
            done |= newly
            maxiteration+=1
            if np.all(done):
                residual=y*expit(-u)-(n-y)*expit(u)-b*invvar
                return b,u,c,maxiteration,float(np.max(np.abs(residual)/np.maximum(1,n)))
            active=~done
            lower=np.where(active & (score>0),point,lower)
            upper=np.where(active & (score<=0),point,upper)
            proposal=point+score/ci;width=upper-lower
            safe=np.isfinite(proposal)&(proposal>lower+.25*width)&(proposal<upper-.25*width)
            proposal=np.where(safe,proposal,(lower+upper)/2)
            point=np.where(active,proposal,point)
    raise RuntimeError('conditional modes failed strict residual gate in both equivalent coordinates')

def modes(eta,y,n,sigma):
    b,u,c,iteration,residual=mode_state(eta,y,n,sigma)
    return b,c,iteration,residual

def objective_gradient(theta,X,y,n):
    X=np.asarray(X,dtype=float);y=np.asarray(y,dtype=float);n=np.asarray(n,dtype=float)
    theta=np.asarray(theta,dtype=float)
    if X.shape!=(len(y),len(theta)-1) or n.shape!=y.shape or np.any(y<0) or np.any(y>n):
        raise ValueError('invalid GLMM arrays')
    eta=X@theta[:-1];sigma=math.exp(theta[-1]);t=1/(sigma*sigma)
    b,u,c,_,_=mode_state(eta,y,n,sigma)
    p=expit(u);pm=expit(-u);v=n*p*pm;a=v*(pm-p)
    kernel=-y*np.logaddexp(0,-u)-(n-y)*np.logaddexp(0,u)
    constants=gammaln(n+1)-gammaln(y+1)-gammaln(n-y+1)
    value=kernel-b*b*t/2-math.log(sigma)-np.log(c)/2+constants
    grad_eta=y*pm-(n-y)*p-a*t/(2*c*c)
    grad_log_sigma=b*b*t-1+t/c-a*b*t/(c*c)
    return -float(value.sum()), -np.r_[X.T@grad_eta,grad_log_sigma.sum()]

def fit_reduced_design(X,y,n):

    X=np.asarray(X,dtype=float)
    results=[]
    for sigma in [.1,.5,2.]:
        initial=np.zeros(X.shape[1]+1);initial[-1]=math.log(sigma)
        fit=minimize(objective_gradient,initial,args=(X,y,n),jac=True,method='L-BFGS-B',
            bounds=[(None,None)]*X.shape[1]+[(-8.,math.log(20.))],
            options={'maxiter':2000,'ftol':1e-12,'gtol':1e-7,'maxls':50})
        results.append(fit)
    best=min(results,key=lambda z:float(z.fun))
    return best,results
