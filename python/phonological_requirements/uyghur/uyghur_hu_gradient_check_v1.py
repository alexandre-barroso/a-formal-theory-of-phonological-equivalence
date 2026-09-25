import numpy as np

def check_gradient(objective, theta, gradient, X):
    theta=np.asarray(theta,dtype=float);gradient=np.asarray(gradient,dtype=float);X=np.asarray(X,dtype=float)
    if X.ndim!=2 or X.shape[1]+1!=len(theta) or theta.shape!=gradient.shape:
        raise ValueError('invalid gradient-check dimensions')
    
    scales=np.r_[np.maximum(1.,np.max(np.abs(X),axis=0)),1.]
    records=[];previous=None
    for radius in [.002,.001,.0005,.00025]:
        steps=radius/scales;numeric=np.empty_like(theta)
        for j,h in enumerate(steps):
            unit=np.zeros_like(theta);unit[j]=h
            numeric[j]=(objective(theta-2*unit)-8*objective(theta-unit)+8*objective(theta+unit)-objective(theta+2*unit))/(12*h)
        change=None if previous is None else float(np.max(abs(numeric-previous)))
        error=float(np.max(abs(numeric-gradient)))
        records.append({'predictor_radius':radius,'steps':steps.tolist(),'numeric':numeric.tolist(),'successive_max_abs':change,'analytic_max_abs_difference':error})
        if previous is not None and change<=1e-4:
            if not np.all(np.isfinite(numeric)) or error>5e-4:
                raise RuntimeError('converged finite-difference check disagrees with analytic gradient: '+repr(records))
            return {'passed':True,'records':records,'max_abs_difference':error,'convergence_difference':change}
        previous=numeric
    raise RuntimeError('finite-difference check did not stabilize: '+repr(records))
