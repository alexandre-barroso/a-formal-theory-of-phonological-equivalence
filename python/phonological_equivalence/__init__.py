"""Exact calculations accompanying *A Formal Theory of Phonological Equivalence*.

The package uses only Python's standard library.  It exposes the finite,
MaxEnt, continuous-HG, contextual, flux, application, and support-selection
calculations used in the dissertation.
"""

from .application_model import (
    BasicSyllableInventory,
    ContinuumMinimum,
    GridMinimum,
    ProfileResult,
    QuadraticObjective,
    QuadraticProfile,
    QuadraticSupportIndex,
)
from .contextual_model import ReplayContextualResult
from .continuous_hg import ReplayContinuousHGResult
from .finite_model import EvaluateFiniteModel
from .flux import ReplayFluxResult
from .maxent import (
    CheckBasicSyllableExactWitness,
    CheckExactConeAlternativeWitness,
    CheckOrderedContactExactWitness,
    CheckResponseEnvelopeExactWitness,
)
from .support_selection import ReplaySupportSelection

__all__ = [
    "BasicSyllableInventory",
    "CheckBasicSyllableExactWitness",
    "CheckExactConeAlternativeWitness",
    "CheckOrderedContactExactWitness",
    "CheckResponseEnvelopeExactWitness",
    "ContinuumMinimum",
    "EvaluateFiniteModel",
    "GridMinimum",
    "ProfileResult",
    "QuadraticObjective",
    "QuadraticProfile",
    "QuadraticSupportIndex",
    "ReplayContextualResult",
    "ReplayContinuousHGResult",
    "ReplayFluxResult",
    "ReplaySupportSelection",
]
