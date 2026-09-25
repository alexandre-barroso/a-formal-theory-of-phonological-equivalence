from pathlib import Path
from dataclasses import dataclass
import datetime
import hashlib
import json
import sympy as sp

REPO = Path(__file__).resolve().parents[3]
O = REPO / 'build/uyghur/algebra'
O.mkdir(parents=True,exist_ok=True)
H, lam, Ucost, Rcost = sp.symbols('H lambda Ucost Rcost', real=True)

@dataclass(frozen=True)
class State:
    previous: int
    final: int | None
    suffix: int | None

def context(state, value):
    trigger = state.final if state.final is not None else state.previous
    return int(trigger == value)

def pressure(state, value, partial=False):
    defined = not (partial and state.suffix is None)
    good = state.suffix == value
    return int(defined and not good)

def harmony(reference, state, mode='retained'):
    out = 0
    for value in [0, 1]:
        p = pressure(state, value, mode == 'partial')
        marked = context(state, value) * p
        initial = context(reference, value) * pressure(reference, value, mode == 'partial')
        out += H * (marked if mode == 'current' else initial * p + lam * (1-initial) * marked)
    return sp.expand(out)

records = []
checks = 0
for old in [0, 1]:
    for previous in [0, 1]:
        ref = State(previous, old, None)
        costs = {}
        for raised in [False, True]:
            for is_old in [True, False]:
                target = old if is_old else 1-old
                state = State(previous, None if raised else old, target)
                actual = harmony(ref, state) + (Rcost if raised else Ucost)
                expected_harmony = (lam * H if is_old else H) if raised and previous != old else (0 if is_old else H)
                assert sp.simplify(actual - expected_harmony - (Rcost if raised else Ucost)) == 0
                partial = harmony(ref, state, 'partial')
                current = harmony(ref, state, 'current')
                assert sp.simplify(partial - lam * current) == 0
                costs[(raised, is_old)] = actual
                records.append({'previous':previous,'old':old,'raised':raised,'suffix_is_old':is_old,'initial_bits':[context(ref,v)*pressure(ref,v) for v in [0,1]],'retained':str(actual),'partial':str(partial),'current':str(current)})
                checks += 2
        unraised_log_odds = sp.expand(costs[(False, False)] - costs[(False, True)])
        raised_log_odds = sp.expand(costs[(True, False)] - costs[(True, True)])
        assert sp.simplify(unraised_log_odds - H) == 0
        assert sp.simplify(raised_log_odds - ((1-lam)*H if previous != old else H)) == 0
        checks += 2
        cross_log_odds = sp.expand(-costs[(True, True)]-costs[(False, False)]+costs[(True, False)]+costs[(False, True)])
        assert sp.simplify(cross_log_odds - (-lam*H if previous != old else 0)) == 0
        checks += 1
        a = (1-lam/2)*H
        b = lam*H/2
        for raised in [False, True]:
            for is_old in [True, False]:
                target = old if is_old else 1-old
                surface_trigger = previous if raised else old
                rival = (Rcost if raised else Ucost) + a*int(target != old) + b*int(target != surface_trigger)
                offset = lam*H/2 if raised and previous != old else 0
                assert sp.simplify(costs[(raised,is_old)]-rival-offset) == 0
                checks += 1

retained_opposed = [Ucost,Ucost+H,Rcost+lam*H,Rcost+H]
retained_agreeing = [Ucost,Ucost+H,Rcost,Rcost+H]
def raise_odds(costs):
    return (sp.exp(-costs[2])+sp.exp(-costs[3]))/(sp.exp(-costs[0])+sp.exp(-costs[1]))
odds_factor = (sp.exp(-lam*H)+sp.exp(-H))/(1+sp.exp(-H))
assert sp.simplify(raise_odds(retained_opposed)/raise_odds(retained_agreeing)-odds_factor) == 0
checks += 1
assert sp.simplify(1-odds_factor-(1-sp.exp(-lam*H))/(1+sp.exp(-H))) == 0
checks += 1
assert sp.simplify((H-(1-lam)*H)/H-lam) == 0
checks += 1


ref = State(0,1,None)
state = State(0,None,0)
assert harmony(ref,state).subs(lam,1) == H
assert harmony(ref,state,'current') == 0
checks += 1
assert all(sp.simplify(x.subs(H,0))==0 for x in [H,(1-lam)*H,lam*H])
checks += 1

record = {
    'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status':'FRAGMENT_ALGEBRA_CHECKS_PASS',
    'checks':checks,
    'derived_candidate_states':len(records),
    'sympy_version':sp.__version__,
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'specification_sha256':hashlib.sha256((REPO/'data/uyghur/specification.json').read_bytes()).hexdigest(),
    'records':records,
    'raising_odds_factor':str(odds_factor),
    'scope':['Assumed two root harmonizers and one suffix target, fixed origins and unit cell multiplicity','Total class-membership consequence at unspecified suffix; alternative partial semantics separately checked','Symbolic identities; corpus mapping, candidate completeness and empirical evaluation are separate obligations','Lean counterparts: PhonologicalCalculus.Application.UyghurJoint and UyghurPredictions'],
    'nonidentifiability':['H=0 erases lambda contrast','Partial initial feature access yields only lambda*H','A free per-root raising offset absorbs the opposed-root lambda*H/2 offset relative to matched input-plus-surface weights'],
}
(O/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='records'},indent=2))
