from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Sequence

from phonological_opacity.fragments.gua import SCHEMAS, GuaFragment, load_spec

from .exact import LinForm
from .guaext import symbolic_score
from .sharedactivity import REPAIRED_CONSTRAINTS, SharedActivityModel

SPEC = load_spec()

RETAINED_VARS = tuple(f"w_{s}" for s in SCHEMAS)
RETAINED_POINT = {f"w_{s}": Fraction(SPEC["weights"][s]) for s in SCHEMAS}
SA_VARS = tuple(f"t_{c}" for c in REPAIRED_CONSTRAINTS)
SA_POSTER_POINT = {
    "t_MARK_ATR": Fraction(23), "t_MARK_HIA": Fraction(22), "t_ID_INIT_V": Fraction(22),
    "t_ID_PLUS_ATR_G": Fraction(21), "t_ID_MINUS_ATR": Fraction(1),
}

CURRENT_VARS = (
    tuple(f"c_{s}" for s in ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE"))
    + tuple(f"c_{s}_{k}" for s in ("H", "A", "GL", "D") for k in ("OLD", "NEW"))
)


@dataclass(frozen=True)
class Retained:

    frag: GuaFragment
    lam: Fraction = Fraction(1, 8)

    name = "RETAINED"

    def variables(self) -> tuple[str, ...]:
        return RETAINED_VARS

    def candidates(self) -> Iterable[tuple[int, tuple[str, ...]]]:
        return self.frag.all_candidates()

    def symbolic(self, segments: Sequence[str]) -> LinForm:
        return symbolic_score(self.frag, segments, prefix="w", lam=self.lam)

    def point(self) -> dict[str, Fraction]:
        return dict(RETAINED_POINT)


@dataclass(frozen=True)
class CurrentMarkedness:

    frag: GuaFragment

    name = "CURRENT-MARKEDNESS"

    def variables(self) -> tuple[str, ...]:
        return CURRENT_VARS

    def candidates(self) -> Iterable[tuple[int, tuple[str, ...]]]:
        return self.frag.all_candidates()

    def symbolic(self, segments: Sequence[str]) -> LinForm:
        F = self.frag
        cur = F.readers(segments)
        ref = F._ref_readers
        out = LinForm.num(0)
        for s in ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE"):
            v = sum(F.marked(cur[s][q]) for q in range(F.n))
            if v:
                out = out + LinForm.var(f"c_{s}") * v
        for s in ("H", "A", "GL", "D"):
            old = new = 0
            for q in range(F.n):
                m = F.marked(cur[s][q])
                if not m:
                    continue
                if F.marked(ref[s][q]):
                    old += 1
                else:
                    new += 1
            if old:
                out = out + LinForm.var(f"c_{s}_OLD") * old
            if new:
                out = out + LinForm.var(f"c_{s}_NEW") * new
        return out

    def point(self) -> dict[str, Fraction] | None:
        return None


@dataclass(frozen=True)
class SharedActivity:

    frag: GuaFragment
    phrase_guard: bool = True
    full_gen: bool = True
    deleted_activity: str = "zero"

    name = "SHARED-ACTIVITY"

    @property
    def _m(self) -> SharedActivityModel:
        return SharedActivityModel(self.frag, phrase_guard=self.phrase_guard,
                                   full_gen=self.full_gen,
                                   deleted_activity=self.deleted_activity)

    def variables(self) -> tuple[str, ...]:
        return SA_VARS

    def candidates(self) -> Iterable[tuple[int, tuple[str, ...]]]:
        return self._m.candidates()

    def symbolic(self, segments: Sequence[str]) -> LinForm:
        return self._m.symbolic_penalty(segments, prefix="t")

    def point(self) -> dict[str, Fraction]:
        return dict(SA_POSTER_POINT)


MODELS = {
    "RETAINED": Retained,
    "CURRENT-MARKEDNESS": CurrentMarkedness,
    "SHARED-ACTIVITY": SharedActivity,
}
