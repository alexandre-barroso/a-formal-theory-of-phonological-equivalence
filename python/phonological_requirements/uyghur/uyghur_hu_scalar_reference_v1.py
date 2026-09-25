import math
from functools import lru_cache
import numpy as np
from scipy.optimize import brentq
from scipy.special import expit,gammaln,logsumexp
from scipy.integrate import quad
from numpy.polynomial.hermite import hermgauss

@lru_cache(None)
def rule(order):
    x,w=hermgauss(order);return x,np.log(w)

def mode(eta,y,n,sigma):
    if n==0:return 0.,1/sigma**2
    inv=1/sigma**2
    lo=np.nextafter((y-n)/inv,-np.inf);hi=np.nextafter(y/inv,np.inf)
    score=lambda b:y*expit(-eta-b)-(n-y)*expit(eta+b)-b*inv
    b=brentq(score,lo,hi,xtol=1e-13,maxiter=300)
    c=n*expit(eta+b)*expit(-eta-b)+inv
    assert abs(score(b))/c<1e-10
    return b,c

def height(b,eta,y,n,sigma):
    u=eta+b
    return -y*np.logaddexp(0,-u)-(n-y)*np.logaddexp(0,u)-b*b/(2*sigma*sigma)-math.log(sigma*math.sqrt(2*math.pi))

def root_law(eta,y,n,sigma,approximation):
    b,c=mode(eta,y,n,sigma);h=height(b,eta,y,n,sigma)
    const=float(gammaln(n+1)-gammaln(y+1)-gammaln(n-y+1))
    if approximation=='laplace':return const+h+.5*math.log(2*math.pi/c)
    if approximation=='gh80':
        x,lw=rule(80);scale=math.sqrt(2/c)
        values=np.array([height(b+scale*z,eta,y,n,sigma)-h+z*z for z in x])
        return const+h+math.log(scale)+float(logsumexp(lw+values))
    if approximation=='direct':
        scale=math.sqrt(c)
        integral,error=quad(lambda z:math.exp(height(b+z/scale,eta,y,n,sigma)-h)/scale,-math.inf,math.inf,epsabs=1e-11,epsrel=1e-11,limit=500)
        assert integral>0 and error<=max(1e-9,integral*1e-8)
        return const+h+math.log(integral)
    raise ValueError(approximation)

def negative_log_likelihood(beta,sigma,X,y,n,approximation):
    return -sum(root_law(float(eta),float(yi),float(ni),sigma,approximation) for eta,yi,ni in zip(np.asarray(X)@np.asarray(beta),y,n))

def root_loglik_quad(beta,sigma,X,y,n):
    assert len(y)==len(n)==len(X)==1
    return root_law(float(np.asarray(X)[0]@np.asarray(beta)),float(y[0]),float(n[0]),sigma,'direct')
