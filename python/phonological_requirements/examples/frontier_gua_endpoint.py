import sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from phonological_requirements import certificate, paths
from phonological_requirements.attenuation_region import exact_region_certificate, exact_instance

proof, records = exact_region_certificate()
points = [F(49,100), F(199,400), F(499,1000), F(4999,10000), F(1,2)]
out = {"exact_region": {"lower": "0", "upper": "1/2", "upper_included": False}, "points": {}}
for lam in points:
    ok, w = exact_instance(lam, proof, records)
    out["points"][str(lam)] = {"feasible": ok, "witness": w}
    print(lam, ok)
certificate.write("frontier_gua_endpoint.json", out, paths.EXAMPLES)
