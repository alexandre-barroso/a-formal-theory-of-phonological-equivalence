from functools import lru_cache
import math
import numpy as np
from numpy.polynomial.hermite import hermgauss
from scipy.special import gammaln, logsumexp
from uyghur_laplace_vectorized_v3 import mode_state

@lru_cache(maxsize=8)
def nodes_weights(order):
    x, w = hermgauss(order)
    x.flags.writeable = False
    logw = np.log(w)
    logw.flags.writeable = False
    return x, logw

def objective(theta, X, y, n, order=80):
    X = np.asarray(X, dtype=float)
    y, n, theta = map(lambda z:np.asarray(z, dtype=float), (y, n, theta))
    if X.shape != (len(y), len(theta)-1) or n.shape != y.shape or np.any(y<0) or np.any(y>n) or order<3:
        raise ValueError('invalid one-row-per-root quadrature arrays')
    eta = X @ theta[:-1]
    sigma = math.exp(theta[-1])
    b, mode_u, c, _, _ = mode_state(eta, y, n, sigma)
    x, logw = nodes_weights(order)
    scale = np.sqrt(2/c)
    shift = b[:,None] + scale[:,None] * x[None,:]
    totaleta = mode_u[:,None] + scale[:,None] * x[None,:]
    height = (-y*np.logaddexp(0,-mode_u) - (n-y)*np.logaddexp(0,mode_u)
              - b*b/(2*sigma*sigma) - math.log(sigma*math.sqrt(2*math.pi)))
    values = (-y[:,None]*np.logaddexp(0,-totaleta) - (n-y)[:,None]*np.logaddexp(0,totaleta)
              - shift*shift/(2*sigma*sigma) - math.log(sigma*math.sqrt(2*math.pi)))
    log_integrals = height + np.log(scale) + logsumexp(logw[None,:] + values-height[:,None]+x[None,:]**2, axis=1)
    const = gammaln(n+1)-gammaln(y+1)-gammaln(n-y+1)
    return -float(np.sum(log_integrals+const))
