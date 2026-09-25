from __future__ import annotations

import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable, Optional, Sequence

from phonological_opacity.fragments.gua import MARKEDNESS, SCHEMAS, GuaFragment

from .models import LocusVector, locus_vector, model_instances as cycle1_instances
from .structures import GuaContext, Skeleton, State


@dataclass(frozen=True)
class Instance:

    id: str
    provenance: str
    parameterisation: str
    parameters: Optional[dict]
    description: str
    predict: Callable[[GuaContext, Skeleton], Optional[list[tuple[str, ...]]]]

    def __post_init__(self) -> None:
        free = self.parameterisation == "parameter_free"
        if free != (self.parameters is None):
            raise ValueError(
                f"{self.id}: parameters must be None exactly when parameter_free")

    def as_record(self) -> dict:
        return {"id": self.id, "provenance": self.provenance,
                "parameterisation": self.parameterisation,
                "parameters": (None if self.parameters is None
                               else {k: str(v) for k, v in self.parameters.items()}),
                "description": self.description}


def predictions_of(ctx: GuaContext, instance: Instance, skeleton: Skeleton,
                   cache: dict) -> Optional[list[tuple[str, ...]]]:
    key = (instance.id, skeleton.key())
    if key not in cache:
        cache[key] = instance.predict(ctx, skeleton)
    return cache[key]


def observation_of(ctx: GuaContext, instance: Instance, skeleton: Skeleton,
                   bridge_fn, cache: Optional[dict] = None) -> Optional[tuple]:
    predicted = (instance.predict(ctx, skeleton) if cache is None
                 else predictions_of(ctx, instance, skeleton, cache))
    if predicted is None:
        return None
    return tuple(sorted({repr(bridge_fn(ctx, State(skeleton, tuple(p)))) for p in predicted}))


def _argmin_predictor(score: Callable[[GuaContext, Skeleton], list[Optional[int]]]):
    def predict(ctx: GuaContext, skeleton: Skeleton):
        candidates = ctx.candidates(skeleton)
        values = score(ctx, skeleton)
        live = [(v, c) for v, c in zip(values, candidates) if v is not None]
        if not live:
            return None
        best = min(v for v, _ in live)
        return [tuple(c.values) for v, c in live if v == best]
    return predict


def _cycle1_predictor(inst) -> Callable:
    def score(ctx: GuaContext, skeleton: Skeleton) -> list[Optional[int]]:
        fragment = ctx.fragment(skeleton, f"c1_{inst.id}")
        return [inst.score8(locus_vector(fragment, list(c.values)))
                for c in ctx.candidates(skeleton)]
    return _argmin_predictor(score)


def cycle1_set(ctx: GuaContext) -> list[Instance]:
    out: list[Instance] = []
    for inst in cycle1_instances(ctx):
        params = dict(inst.weights)
        params["lambda"] = inst.lam
        out.append(Instance(
            id=inst.id, provenance=inst.provenance,
            parameterisation="shared_weight_vector", parameters=params,
            description=inst.description, predict=_cycle1_predictor(inst)))
    return out


P2_VARIANT_NOTES = {
    "baseline": "appendix I's rendering of the appendix G declaration; an internal control that "
                "must land in RET's class",
    "def_eq_context": "Def := C for every markedness schema. The generic repair the specification "
                      "rules out in advance; a negative control",
    "dynamic_next_word": "the A relatum resolves to the immediately next present origin inside the "
                         "next word",
    "dynamic_phrase": "the same policy scoped to the phrase rather than the next word",
    "dynamic_nucleus": "a nuclear-nonhigh filter in skip mode; a failed repair",
    "dynamic_stop_nucleus": "the same filter in stop mode",
    "origin_bound": "the relatum is the reference-selected partner, tracked to its realisation",
    "witness": "the relation instance selected in the reference, transported while its conditions hold",
    "witness_phrase": "the witness policy scoped to the phrase",
}


def p2_set(ctx: GuaContext) -> tuple[list[Instance], dict]:
    from phonological_grounding.declaration_language.adequacy import l_locus_terms, l_readers
    from phonological_grounding.declaration_language.gua_decls import SCHEMA_ORDER, signature_from_spec
    from phonological_grounding.declaration_language.variants import VARIANTS, build_declarations

    base_weights = {s: Fraction(ctx.shared["weights"][s]) for s in SCHEMAS}
    lam = Fraction(ctx.shared["lambda"]["num"], ctx.shared["lambda"]["den"])

    def make(name: str) -> Instance:
        decls = build_declarations(name)

        def score(c: GuaContext, skeleton: Skeleton) -> list[Optional[int]]:
            fragment = c.fragment(skeleton, f"p2_{name}")
            shim = dict(c.shared)
            shim["inputs"] = list(c.shared["inputs"]) + [fragment.record]
            sig = signature_from_spec(shim, fragment.record)
            ref = l_readers(sig, fragment.reference, fragment.reference, decls)
            values: list[Optional[int]] = []
            for cand in c.candidates(skeleton):
                terms = l_locus_terms(sig, fragment.reference, list(cand.values),
                                      decls, ref, MARKEDNESS)
                total = Fraction(0)
                for schema in SCHEMA_ORDER:
                    old, new = terms[schema]
                    total += base_weights[schema] * (Fraction(old) + lam * new)
                scaled = total * 8
                values.append(int(scaled) if scaled.denominator == 1 else None)
            return values

        params = dict(base_weights)
        params["lambda"] = lam
        return Instance(
            id=f"P2:{name}", provenance="P2_RESOLVER_SEMANTICS_v1",
            parameterisation="shared_weight_vector", parameters=params,
            description=P2_VARIANT_NOTES.get(name, name),
            predict=_argmin_predictor(score))

    return [make(n) for n in VARIANTS], dict(VARIANTS)


EXCLUDED = [
    {"id": "CURRENT-MARKEDNESS (appendix J's reconstruction)",
     "reason": "its `point()` returns None: the reconstruction leaves the OLD and NEW weights free "
               "and the source supplies no declared parameter point. Choosing one here would be "
               "inventing a model. The dissertation's own strictly-current-markedness comparator at "
               "the declared weight vector is already in M as `CUR`, labelled as such.",
     "registry_status": "reconstructed, parameters free"},
    {"id": "SHARED-ACTIVITY (repaired)",
     "reason": "the REPAIR introduces faithfulness constraints whose weights the poster does not "
               "declare. `SA_POSTER_POINT` pins only the poster's five constraints, so evaluating "
               "the repaired model at it raises `unbound parameter 't_MAX'`; appendix J's own "
               "search treats t_MAX as free (see data/predictions/results/designs/"
               "separation_length.json, where it ranges over 1, 5/2, 10/3, 5). There is therefore no "
               "declared point covering its parameter set, and picking one would be inventing the "
               "model. The UNREPAIRED five-constraint version IS covered by the poster point, but "
               "appendix J records that it cannot reproduce its own source's winner, so including "
               "it would be uncharitable rather than honest.",
     "registry_status": "reconstructed and repaired; parameters of the repair free",
     "what_would_admit_it": "a declared parameter point from appendix J, OR extending this "
               "measurement from point instances to PARAMETER-REGION instances, whose observation is "
               "the set of outputs attainable over the region. The second is the specification's "
               "target Q4 and is the named next step; it is not improvised here."},
    {"id": "LOCAL-EVALUATOR",
     "reason": "no implementation is published in appendix J's tree and the registry supplies no "
               "parameter point, so it cannot be evaluated on the licensed protocols.",
     "registry_status": "reconstructed, not implemented"},
    {"id": "STRATAL-CLASSICAL, STRATAL-WEAK",
     "reason": "one ranking or weighting PER STRATUM, with no declared point; not evaluable without "
               "inventing the strata's parameters.",
     "registry_status": "reconstructed, parameters free"},
    {"id": "RETAINED-DOMAIN-BOUNDED, RETAINED-ORIGIN-BOUND, RETAINED-WITNESS-PRESERVING",
     "reason": "registry status UNRESOLVED for generator, observer and parameters. The reviewer's "
               "instruction is explicit: do not guess a model into existence to enlarge a count.",
     "registry_status": "UNRESOLVED"},
    {"id": "GRAPH-35, GRAPH-36-UNIFORM, LINK-POTENTIAL, DIRECTIONAL-LINEAR-SITE",
     "reason": "their declared domains are Lithuanian graph products, Odawa, or the continuous "
               "track; none of them predicts an output for a Gua focal product, so they are not "
               "instances of THIS protocol family.",
     "registry_status": "out of domain for the Gua battery"},
]


def p3_set(ctx: GuaContext) -> list[Instance]:
    from phonological_grounding.predictions.ruleserial import RuleSerial

    def rule_serial(c: GuaContext, skeleton: Skeleton):
        fragment = c.fragment(skeleton, "p3_ruleserial")
        try:
            return [tuple(RuleSerial(fragment).derive())]
        except (ValueError, KeyError):
            return None

    return [
        Instance(id="P3:RULE-SERIAL", provenance="P3_RIVAL_REGISTRY_v1",
                 parameterisation="parameter_free", parameters=None,
                 description="harmony then hiatus resolution as ordered rewriting; no free "
                             "parameters at all, and not a candidate competition. Its prediction is "
                             "undefined beyond four lexical words, where the phrasing rule is "
                             "undefined, rather than guessed",
                 predict=rule_serial),
    ]


def enlarged_set(ctx: GuaContext) -> list[Instance]:
    return cycle1_set(ctx) + p2_set(ctx)[0] + p3_set(ctx)
