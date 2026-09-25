from __future__ import annotations

from phonological_opacity.gua.grammar import INPUTS_DELETION, INPUTS_SELECTION

from .indep_gua import Product


def gua_products():
    out = []
    for inputs in (INPUTS_SELECTION, INPUTS_DELETION):
        for u in inputs:
            out.append((tuple(u["focal"]),
                        Product(u["id"], [x["phone"] for x in u["slots"]],
                                [x["word"] for x in u["slots"]], u["phrases"],
                                u["focal"])))
    return out


def gua_observations():
    from phonological_opacity.gua.observations import OBSERVATIONS_DELETION, OBSERVATIONS_SELECTION
    obs = {}
    for table in (OBSERVATIONS_SELECTION, OBSERVATIONS_DELETION):
        for o in table:
            obs[o["id"]] = o
    return obs
