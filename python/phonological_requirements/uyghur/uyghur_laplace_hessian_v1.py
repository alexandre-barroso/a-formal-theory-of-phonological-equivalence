import math
import numpy as np
from scipy.special import expit
from uyghur_laplace_vectorized_v3 import mode_state

def hessian(theta,X,y,n):
    theta,X,y,n=map(lambda z:np.asarray(z,dtype=float),(theta,X,y,n))
    t=math.exp(-2*theta[-1]);eta=X@theta[:-1]
    b,u,c,_,_=mode_state(eta,y,n,math.exp(theta[-1]))
    p=expit(u);pm=expit(-u);v=n*p*pm;a=v*(pm-p);d=v*((pm-p)**2-2*p*pm)
    he=-v*t/c-.5*t*t*d/c**3+a*a*t*t/c**4
    cross=-2*b*v*t/c-b*d*t*t/c**3+a*t/c**2+2*a*a*b*t*t/c**4-2*a*t*t/c**3
    hs=4*b*b*t*t/c-2*b*b*t-2*t/c+2*t*t/c**2-2*d*b*b*t*t/c**3+2*a*b*t/c**2-8*a*b*t*t/c**3+4*a*a*b*b*t*t/c**4
    result=np.empty((len(theta),len(theta)))
    result[:-1,:-1]=X.T@(he[:,None]*X)
    result[:-1,-1]=X.T@cross;result[-1,:-1]=result[:-1,-1]
    result[-1,-1]=hs.sum()
    return -result
