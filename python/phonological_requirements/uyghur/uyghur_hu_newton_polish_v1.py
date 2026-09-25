import math
import numpy as np
from scipy.optimize import OptimizeResult

def difference_hessian(gradient,theta,X):
    scales=np.r_[np.maximum(1.,np.max(np.abs(X),axis=0)),1.]
    columns=[]
    for j,h in enumerate(.001/scales):
        e=np.zeros(len(theta));e[j]=h
        columns.append((gradient(theta-2*e)-8*gradient(theta-e)+8*gradient(theta+e)-gradient(theta+2*e))/(12*h))
    H=np.column_stack(columns)
    return (H+H.T)/2

def polish(initial,objective_gradient,hessian,maxiter=120):
    theta=np.asarray(initial,dtype=float).copy();low,high=-8.,math.log(20.)
    if not low<=theta[-1]<=high:raise ValueError('initial variance outside frozen bounds')
    history=[];success=False;message='maximum polishing iterations reached'
    for iteration in range(maxiter):
        value,g=objective_gradient(theta);g=np.asarray(g,dtype=float);H=np.asarray(hessian(theta),dtype=float)
        if not np.isfinite(value) or not np.all(np.isfinite(g)) or not np.all(np.isfinite(H)):
            message='nonfinite numerical evaluation';break
        active=(theta[-1]<=low+1e-10 and g[-1]>=0) or (theta[-1]>=high-1e-10 and g[-1]<=0)
        free=np.arange(len(theta)-int(active));projected=g.copy()
        if active:projected[-1]=0.
        eigen,vectors=np.linalg.eigh(H[np.ix_(free,free)])
        step=np.zeros_like(theta);step[free]=-vectors@((vectors.T@g[free])/np.maximum(eigen,1e-12))
        if theta[-1]<=low+1e-10 and step[-1]<0:step[-1]=0.
        if theta[-1]>=high-1e-10 and step[-1]>0:step[-1]=0.
        if g@step>=0:step=-projected
        decrement=-float(g@step);pg=float(max(abs(projected)))
        history.append({'iteration':iteration,'objective':float(value),'projected_gradient_max':pg,'newton_decrement':decrement,'min_free_hessian_eigenvalue':float(min(eigen))})
        if pg<=1e-7 and decrement<=1e-8:
            success=True;message='projected gradient and Newton decrement converged';break
        norm=np.linalg.norm(step)
        if norm>10000:step*=10000/norm
        alpha=1.
        if step[-1]>0:alpha=min(alpha,max(0.,(high-theta[-1])/step[-1]))
        elif step[-1]<0:alpha=min(alpha,max(0.,(low-theta[-1])/step[-1]))
        accepted=False
        for backtrack in range(60):
            trial=theta+alpha*step;trial[-1]=np.clip(trial[-1],low,high)
            fv,_=objective_gradient(trial)
            if np.isfinite(fv) and fv<=value+1e-4*alpha*(g@step) and alpha>0:
                accepted=True;break
            alpha*=.5
        if not accepted:message='polishing line search failed';break
        theta=trial
    value,g=objective_gradient(theta)
    return OptimizeResult(x=theta,fun=float(value),jac=np.asarray(g),success=success,message=message,nit=iteration+1,polish_history=history)
