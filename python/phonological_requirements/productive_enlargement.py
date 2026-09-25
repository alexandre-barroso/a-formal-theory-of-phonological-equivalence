from __future__ import annotations

from phonological_requirements import certificate
from phonological_requirements.productive import ProductiveSearch
from phonological_requirements.products import gua_observations, gua_products


def main() -> int:
    obs = gua_observations()
    rec = {}
    for _, prod in gua_products():
        best, minima, _, cert = ProductiveSearch(prod).minimise()
        outputs = sorted({prod.observe(m) for m in minima})
        allowed = set(obs[prod.id]["allowed"])
        rec[prod.id] = {"best": str(best), "minima": [list(m) for m in minima], "outputs": outputs,
                        "exclusive": len(minima) == 1 and all(o in allowed for o in outputs), "cert": cert}
        print(prod.id, best, outputs, cert["search_space"], cert["leaves_scored"], cert["coverage_identity"])
    certificate.write("productive_enlargement.json", rec)
    return 0 if all(v["exclusive"] and v["cert"]["coverage_identity"] for v in rec.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
