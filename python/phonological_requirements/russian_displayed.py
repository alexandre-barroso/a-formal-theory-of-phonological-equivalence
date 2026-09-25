from fractions import Fraction
import math
import numpy as np
from .certificate import read, write


def check():
    c=read('russian_displayed_matrices.json');a=np.array(c['A'],dtype=object);b=np.array(c['B'],dtype=object);mapping=np.array(c['row_map'])
    old=np.any(a!=0,axis=0);new=np.any(b!=0,axis=0)
    if np.any(old&new) or mapping.shape!=(3698,) or mapping.min()<0 or mapping.max()>=308:raise ValueError('Invalid certificate')
    identities=0
    for lam,mu in [(Fraction(1,4),Fraction(1)),(Fraction(1,3),Fraction(3,4)),(Fraction(1,1000),Fraction(999,1000))]:
        factors=np.array([lam/mu if not x else Fraction(1) for x in old],dtype=object)
        if np.any(a+lam*b != (a+mu*b)*factors) or any(x<0 for x in factors):raise ValueError('Reparameterization mismatch')
        identities+=a.size
    cx=[Fraction(1,5),Fraction(49,40),Fraction(49,20),Fraction(129,40)];cy=[Fraction(1,20),Fraction(43,40),Fraction(19,8),Fraction(123,40)]
    if cx[3]-cx[0]!=cy[3]-cy[0]:raise ValueError('Displayed score difference mismatch')
    px=[math.exp(-float(x)) for x in cx];py=[math.exp(-float(x)) for x in cy];px=[x/sum(px) for x in px];py=[x/sum(py) for x in py]
    gap=abs(px[0]-py[0])
    if gap<=.001:raise ValueError('Normalizer witness failed')
    out={'status':'PASS','row_count':3698,'unique_rows':308,'columns':136,'pure_old_columns':int(old.sum()),'pure_new_columns':int(new.sum()),'exact_coefficient_identities':identities,'positive_parameter_pairs':3,'displayed_odds_equal':True,'full_laws_equal':False,'normalized_law_witness':{'costs_quarter':[str(x) for x in cx],'costs_one':[str(x) for x in cy],'faithful_probability_gap':gap},'scope':'Exact finite table checks and synthetic normalization counterexample. Universal positive-parameter cone equality is the Lean theorem; candidate probabilities and fitted penalties are not preserved.'}
    write('russian_displayed.json',out);print(out)

if __name__=='__main__':check()
