import json, math, sys, time
from fractions import Fraction as F
from math import erfc, sqrt
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from phonological_requirements import certificate, paths
from phonological_requirements.tone_sandhi import fit, toks, fit_continuous
from phonological_requirements.observations import SANDHI
t0 = time.time()
tables = {n: {tuple(toks(ur)): srs for ur, srs in exp["table"].items()} for n, exp in SANDHI.items()}
frees = {n: ["S33", "IDENT_REG", "IDENT_CONT", exp["feeding"]] for n, exp in SANDHI.items()}
grid = [F(i, 40) for i in range(0, 41)]
sep = {}
for n, tb in tables.items():
    prof = {lam: fit(tb, lam, frees[n])[1] for lam in grid}
    best = max(prof, key=prof.get); sep[n] = (best, prof[best], prof)
shared = {lam: sep["experiment_1"][2][lam] + sep["experiment_2"][2][lam] for lam in grid}
best_shared = max(shared, key=shared.get); sep_total = sep["experiment_1"][1] + sep["experiment_2"][1]
dev = 2 * (sep_total - shared[best_shared])
out = {"question": "one shared attenuation against separate experimental attenuations with weights free by experiment", "grid": "lambda in {i/40}",
       "separate": {n: {"lambda_grid_best": str(v[0]), "loglik": round(v[1], 3)} for n, v in sep.items()},
       "shared_lambda_grid_best": str(best_shared), "shared_loglik": round(shared[best_shared], 3), "separate_total_loglik": round(sep_total, 3),
       "deviance_shared_vs_separate": round(dev, 3), "df": 1, "independent_token_chi2_reference_p": (erfc(sqrt(dev / 2)) if dev > 0 else 1.0),
       "shared_profile": {str(l): round(v, 3) for l, v in shared.items()}, "seconds": round(time.time() - t0, 1)}
continuous_separate=fit_continuous(tables,frees,shared=False)
continuous_shared=fit_continuous(tables,frees,shared=True)
out["continuous"]={"separate":continuous_separate,"shared":continuous_shared,
                   "deviance_shared_vs_separate":2*(continuous_separate["loglik"]-continuous_shared["loglik"])}
out["statistical_scope"]="The chi-square tail is only an independent-token reference calculation. Repeated speaker/item observations and five overlapping participants are not modeled; process and experimental occasion are confounded."
certificate.write("frontier_lambda_grain.json", out, paths.EXAMPLES)
print({k: v for k, v in out.items() if k != "shared_profile"})
