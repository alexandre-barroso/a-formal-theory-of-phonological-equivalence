from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from phonological_opacity.fragments.gua import SCHEMAS, GuaFragment, load_spec

from .exact import Ineq, LinForm

_SPEC = load_spec()


@dataclass(frozen=True)
class ConstructedInput:

    id: str
    words: tuple[tuple[str, ...], ...]
    phrases: tuple[int, ...]
    focal: tuple[int, ...]
    note: str = ""

    def record(self, observation: str = "") -> dict:
        return {
            "id": self.id,
            "words": [list(w) for w in self.words],
            "phrases": list(self.phrases),
            "focal": list(self.focal),
            "observation": observation,
            "source": "CONSTRUCTED (appendix J design generator)",
        }


def fragment(ci: ConstructedInput, observation: str = "") -> GuaFragment:
    shim = dict(_SPEC)
    shim["inputs"] = list(_SPEC["inputs"]) + [ci.record(observation)]
    return GuaFragment(shim, ci.id)


def named_fragment(input_id: str) -> GuaFragment:
    return GuaFragment(_SPEC, input_id)


def observation_of(input_id: str) -> str:
    return next(u for u in _SPEC["inputs"] if u["id"] == input_id)["observation"]


def symbolic_score(
    frag: GuaFragment,
    segments: Sequence[str],
    *,
    prefix: str = "w",
    lam: LinForm | Fraction | None = None,
) -> LinForm:
    lam_val = frag.lam if lam is None else (lam if isinstance(lam, Fraction) else lam)
    if not isinstance(lam_val, Fraction):
        raise TypeError("symbolic_score needs a rational lambda; use symbolic_score_bilinear")
    terms = frag.locus_terms(segments)
    out = LinForm.num(0)
    for s in SCHEMAS:
        old, new = terms[s]
        c = Fraction(old) + lam_val * Fraction(new)
        if c:
            out = out + LinForm.var(f"{prefix}_{s}") * c
    return out


def symbolic_score_bilinear(frag: GuaFragment, segments: Sequence[str]) -> dict[str, tuple[int, int]]:
    return dict(frag.locus_terms(segments))


def selection_system(
    frag: GuaFragment,
    correct_fibre: Sequence[int],
    *,
    prefix: str = "w",
    lam: Fraction | None = None,
    nonneg: bool = True,
) -> list[Ineq]:
    raise NotImplementedError


def selection_for_representative(
    frag: GuaFragment,
    rep: int,
    fibre: Sequence[int],
    *,
    prefix: str = "w",
    lam: Fraction | None = None,
    nonneg: bool = True,
) -> list[Ineq]:
    if rep not in set(fibre):
        raise ValueError("representative outside the correct fibre")
    lam_val = frag.lam if lam is None else lam
    rep_form = symbolic_score(frag, frag.candidate(rep), prefix=prefix, lam=lam_val)
    fib = set(fibre)
    rows: list[Ineq] = []
    if nonneg:
        for s in SCHEMAS:
            rows.append(Ineq(LinForm.var(f"{prefix}_{s}"), False, f"nonneg:{s}"))
    for i in range(frag.size):
        if i in fib:
            continue
        rival = symbolic_score(frag, frag.candidate(i), prefix=prefix, lam=lam_val)
        rows.append(Ineq(rival - rep_form, True, f"{frag.id}:{rep}<{i}"))
    return rows


def correct_fibre(frag: GuaFragment, observation: str) -> list[int]:
    return [i for i in range(frag.size) if frag.observe(frag.candidate(i)) == observation]
