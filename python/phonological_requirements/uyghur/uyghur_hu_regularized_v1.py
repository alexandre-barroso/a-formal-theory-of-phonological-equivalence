import math
import numpy as np
import uyghur_laplace_vectorized_v3 as laplace
import uyghur_laplace_hessian_v1 as laplace_hessian
import uyghur_gh_gradient_v3 as gh
from uyghur_hu_newton_polish_v1 import difference_hessian

def data_objective_gradient(theta,X,y,n,approximation='laplace'):
    if approximation=='laplace':return laplace.objective_gradient(theta,X,y,n)
    if approximation=='gh80':return gh.objective_gradient(theta,X,y,n,80)
    raise ValueError('unknown frozen likelihood approximation')

def objective_gradient(theta,X,y,n,tau,approximation='laplace'):
    theta=np.asarray(theta,dtype=float)
    if not math.isfinite(tau) or tau<=0:raise ValueError('positive finite native prior scale required')
    value,gradient=data_objective_gradient(theta,X,y,n,approximation)
    gradient=np.asarray(gradient,dtype=float).copy()
    penalty=float(theta[:-1]@theta[:-1])/(2*tau*tau)
    gradient[:-1]+=theta[:-1]/(tau*tau)
    return value+penalty,gradient

def hessian(theta,X,y,n,tau,approximation='laplace'):
    theta=np.asarray(theta,dtype=float)
    if not math.isfinite(tau) or tau<=0:raise ValueError('positive finite native prior scale required')
    if approximation=='laplace':H=laplace_hessian.hessian(theta,X,y,n)
    elif approximation=='gh80':
        H=difference_hessian(lambda t:data_objective_gradient(t,X,y,n,'gh80')[1],theta,X)
    else:raise ValueError('unknown frozen likelihood approximation')
    H=H.copy();indices=np.arange(len(theta)-1);H[indices,indices]+=1/(tau*tau)
    return H

def components(theta,X,y,n,tau,approximation='laplace'):
    theta=np.asarray(theta,dtype=float);data_value,data_gradient=data_objective_gradient(theta,X,y,n,approximation)
    penalty=float(theta[:-1]@theta[:-1])/(2*tau*tau)
    return {'data_negative_log_likelihood':float(data_value),'gaussian_penalty':penalty,'penalized_objective':float(data_value+penalty),'unpenalized_gradient':np.asarray(data_gradient).tolist(),'tau':float(tau),'penalized_fixed_effect_coordinates':len(theta)-1,'prior_normalizing_constant_omitted':True}
