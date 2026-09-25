import math
import numpy as np
from scipy.special import expit, gammaln, logsumexp
from uyghur_laplace_vectorized_v3 import mode_state
from uyghur_gh_vectorized_v3 import nodes_weights

def objective_gradient(theta, X, y, n, order=80):
    X = np.asarray(X, dtype=float)
    y, n, theta = map(lambda z:np.asarray(z, dtype=float), (y, n, theta))
    if X.shape != (len(y), len(theta)-1) or n.shape != y.shape or np.any(y<0) or np.any(y>n) or order<3:
        raise ValueError('invalid one-row-per-root quadrature arrays')
    eta = X @ theta[:-1]
    sigma = math.exp(theta[-1]); t = 1/(sigma*sigma)
    b, mode_u, c, _, _ = mode_state(eta, y, n, sigma)
    x, logw = nodes_weights(order)
    scale = np.sqrt(2/c)
    delta = scale[:,None]*x[None,:]
    z = b[:,None]+delta
    u = mode_u[:,None]+delta
    logkernel = (-y[:,None]*np.logaddexp(0,-u) - (n-y)[:,None]*np.logaddexp(0,u)
                 - z*z*t/2 - math.log(sigma*math.sqrt(2*math.pi)))
    logterms = logw[None,:]+logkernel+x[None,:]**2
    logmass = logsumexp(logterms,axis=1)
    weights = np.exp(logterms-logmass[:,None])
    value = logmass+np.log(scale)+gammaln(n+1)-gammaln(y+1)-gammaln(n-y+1)
    p = expit(mode_u); pm=expit(-mode_u); v = n*p*pm; a=v*(pm-p)
    db_eta = -v/c
    dc_eta = a*t/c
    db_logsigma = 2*b*t/c
    dc_logsigma = a*db_logsigma-2*t
    dz_eta = db_eta[:,None]-delta*(dc_eta/c)[:,None]/2
    dz_logsigma = db_logsigma[:,None]-delta*(dc_logsigma/c)[:,None]/2
    observation_score = y[:,None]*expit(-u)-(n-y)[:,None]*expit(u)
    posterior_score = observation_score-z*t
    eta_gradient = np.sum(weights*(observation_score+posterior_score*dz_eta),axis=1)-dc_eta/(2*c)
    logsigma_gradient = np.sum(weights*(z*z*t-1+posterior_score*dz_logsigma),axis=1)-dc_logsigma/(2*c)
    return -float(value.sum()), -np.r_[X.T@eta_gradient,logsigma_gradient.sum()]
