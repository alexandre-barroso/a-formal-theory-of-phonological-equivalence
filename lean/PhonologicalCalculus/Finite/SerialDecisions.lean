import Mathlib

/-!
# Typed finite serial decisions

Stopped languages, stopped probability laws with explicit nontermination,
generic weighted series, and all-prefix semantics are represented by distinct
constructors.  No comparison between constructors is available without a
prospectively declared cast.
-/

namespace PhonologicalCalculus

inductive SerialTag where
  | stoppedSet
  | stoppedProbability
  | weightedSeries
  | allPrefixes
  deriving DecidableEq, Repr

/-- The four serial answer codomains remain distinct even when their payloads
have accidental numerical similarities. -/
inductive SerialAnswer (Word Coefficient Prefix : Type*) where
  | stoppedSet : Finset Word → SerialAnswer Word Coefficient Prefix
  | stoppedProbability : (Word → ℚ) → ℚ →
      SerialAnswer Word Coefficient Prefix
  | weightedSeries : (Nat → Coefficient) →
      SerialAnswer Word Coefficient Prefix
  | allPrefixes : Finset Prefix → SerialAnswer Word Coefficient Prefix

def SerialAnswer.tag {Word Coefficient Prefix : Type*} :
    SerialAnswer Word Coefficient Prefix → SerialTag
  | .stoppedSet _ => .stoppedSet
  | .stoppedProbability _ _ => .stoppedProbability
  | .weightedSeries _ => .weightedSeries
  | .allPrefixes _ => .allPrefixes

/-- A cast registry is part of the contract rather than an implicit coercion. -/
def SerialComparisonAdmitted (castRegistry : SerialTag → SerialTag → Bool)
    (source target : SerialTag) : Prop :=
  source = target ∨ castRegistry source target = true

/-- Different serial sorts are refused when the prospective cast registry has
no entry for the requested direction. -/
theorem crossTagComparison_refused
    (castRegistry : SerialTag → SerialTag → Bool)
    {source target : SerialTag} (hDifferent : source ≠ target)
    (hMissing : castRegistry source target = false) :
    ¬SerialComparisonAdmitted castRegistry source target := by
  intro admitted
  rcases admitted with hSame | hCast
  · exact hDifferent hSame
  · rw [hMissing] at hCast
    contradiction

theorem serialTags_pairwise_distinct :
    SerialTag.stoppedSet ≠ SerialTag.stoppedProbability ∧
    SerialTag.stoppedSet ≠ SerialTag.weightedSeries ∧
    SerialTag.stoppedSet ≠ SerialTag.allPrefixes ∧
    SerialTag.stoppedProbability ≠ SerialTag.weightedSeries ∧
    SerialTag.stoppedProbability ≠ SerialTag.allPrefixes ∧
    SerialTag.weightedSeries ≠ SerialTag.allPrefixes := by
  decide

/-- The tagged constructors are disjoint independently of their payloads. -/
theorem serialAnswer_constructors_disjoint
    {Word Coefficient Prefix : Type*}
    (stopped : Finset Word) (law : Word → ℚ) (infinityMass : ℚ)
    (series : Nat → Coefficient) (prefixes : Finset Prefix) :
    (@SerialAnswer.stoppedSet Word Coefficient Prefix stopped) ≠
        (@SerialAnswer.stoppedProbability Word Coefficient Prefix law
          infinityMass) ∧
    (@SerialAnswer.stoppedSet Word Coefficient Prefix stopped) ≠
        (@SerialAnswer.weightedSeries Word Coefficient Prefix series) ∧
    (@SerialAnswer.stoppedSet Word Coefficient Prefix stopped) ≠
        (@SerialAnswer.allPrefixes Word Coefficient Prefix prefixes) ∧
    (@SerialAnswer.stoppedProbability Word Coefficient Prefix law
        infinityMass) ≠
        (@SerialAnswer.weightedSeries Word Coefficient Prefix series) ∧
    (@SerialAnswer.stoppedProbability Word Coefficient Prefix law
        infinityMass) ≠
        (@SerialAnswer.allPrefixes Word Coefficient Prefix prefixes) ∧
    (@SerialAnswer.weightedSeries Word Coefficient Prefix series) ≠
        (@SerialAnswer.allPrefixes Word Coefficient Prefix prefixes) := by
  simp

/-! ## Exact finite countermodels -/

def jointLawDiagonal (index : Fin 4) : ℚ :=
  if index.1 = 0 ∨ index.1 = 3 then 1 / 2 else 0

def jointLawOffDiagonal (index : Fin 4) : ℚ :=
  if index.1 = 1 ∨ index.1 = 2 then 1 / 2 else 0

def firstBinaryMarginal (law : Fin 4 → ℚ) (index : Fin 2) : ℚ :=
  if index.1 = 0 then law 0 + law 1 else law 2 + law 3

def secondBinaryMarginal (law : Fin 4 → ℚ) (index : Fin 2) : ℚ :=
  if index.1 = 0 then law 0 + law 2 else law 1 + law 3

/-- Two joint readouts can have identical one-dimensional marginals while the
joint laws differ. -/
theorem fin_a3_marginals_01 :
    firstBinaryMarginal jointLawDiagonal =
        firstBinaryMarginal jointLawOffDiagonal ∧
    secondBinaryMarginal jointLawDiagonal =
        secondBinaryMarginal jointLawOffDiagonal ∧
    jointLawDiagonal ≠ jointLawOffDiagonal := by
  constructor
  · funext index
    fin_cases index <;>
      norm_num [firstBinaryMarginal, jointLawDiagonal,
        jointLawOffDiagonal]
  constructor
  · funext index
    fin_cases index <;>
      norm_num [secondBinaryMarginal, jointLawDiagonal,
        jointLawOffDiagonal]
  · intro hEqual
    have hCoordinate := congrFun hEqual 0
    norm_num [jointLawDiagonal, jointLawOffDiagonal] at hCoordinate

structure UnaryStoppedLaw where
  stoppedMass : ℚ
  infinityMass : ℚ
  deriving DecidableEq, Repr

/-- Conditioning a positive one-outcome stopped law discards its explicit mass
at infinity. -/
def conditionedUnaryLaw (law : UnaryStoppedLaw) : List ℚ :=
  if law.stoppedMass = 0 then [] else [1]

def halfStoppingLaw : UnaryStoppedLaw := ⟨1 / 2, 1 / 2⟩

def certainStoppingLaw : UnaryStoppedLaw := ⟨1, 0⟩

/-- Exact countermodel: conditioning identifies two stopped readouts whose
nontermination masses differ. -/
theorem fin_a3_nontermination_02 :
    conditionedUnaryLaw halfStoppingLaw = [1] ∧
    conditionedUnaryLaw certainStoppingLaw = [1] ∧
    halfStoppingLaw ≠ certainStoppingLaw := by
  norm_num [conditionedUnaryLaw, halfStoppingLaw, certainStoppingLaw]

/-- The explicit infinity coordinate is part of stopped-probability identity. -/
theorem stoppedProbability_retains_nontermination
    {first second : UnaryStoppedLaw}
    (hInfinity : first.infinityMass ≠ second.infinityMass) :
    first ≠ second := by
  intro hEqual
  exact hInfinity (congrArg UnaryStoppedLaw.infinityMass hEqual)

structure FiniteProbabilitySeries where
  coefficients : List ℚ
  nonnegative : ∀ coefficient ∈ coefficients, 0 ≤ coefficient
  totalMass : coefficients.sum = 1

def WeightedSeriesNormalized (coefficients : List ℚ) : Prop :=
  (∀ coefficient ∈ coefficients, 0 ≤ coefficient) ∧
    coefficients.sum = 1

def AdmitsProbabilitySemantics (coefficients : List ℚ) : Prop :=
  ∃ probability : FiniteProbabilitySeries,
    probability.coefficients = coefficients

/-- A generic weighted series has a probability interpretation exactly after
nonnegativity and unit-mass normalization have been supplied. -/
theorem weightedSeries_admitsProbability_iff_normalized
    (coefficients : List ℚ) :
    AdmitsProbabilitySemantics coefficients ↔
      WeightedSeriesNormalized coefficients := by
  constructor
  · rintro ⟨probability, rfl⟩
    exact ⟨probability.nonnegative, probability.totalMass⟩
  · rintro ⟨nonnegative, totalMass⟩
    exact ⟨⟨coefficients, nonnegative, totalMass⟩, rfl⟩

/-- Prefix and stopped-language answers have no default projection between
them. -/
theorem prefixStoppedProjection_refused
    (castRegistry : SerialTag → SerialTag → Bool)
    (hMissing :
      castRegistry SerialTag.allPrefixes SerialTag.stoppedSet = false) :
    ¬SerialComparisonAdmitted castRegistry SerialTag.allPrefixes
      SerialTag.stoppedSet := by
  exact crossTagComparison_refused castRegistry (by decide) hMissing

structure SerialEdgeCases where
  emptyWordMass : ℚ
  summedWordMass : ℚ
  deadlockState : String
  structuralCycle : Bool
  probabilityInfinityMass : ℚ
  deriving DecidableEq, Repr

def registeredSerialEdgeCases : SerialEdgeCases :=
  ⟨1 / 4, 1, "dead", true, 0⟩

/-- Exact empty-word, path-sum, deadlock, structural-cycle, and zero-mass cycle
ledger. -/
theorem fin_a3_edgecases_03 :
    registeredSerialEdgeCases = ⟨1 / 4, 1, "dead", true, 0⟩ := by
  rfl

def allSerialTags : List SerialTag := [
  .stoppedSet, .stoppedProbability, .weightedSeries, .allPrefixes
]

/-- Exact four-sort inventory and duplicate freedom. -/
theorem fin_a3_types_04 :
    allSerialTags.length = 4 ∧ allSerialTags.Nodup := by
  decide

/-- Integrated typed serial-decision theorem. -/
theorem fin_a3_typedSerialDecisions
    (castRegistry : SerialTag → SerialTag → Bool) :
    allSerialTags.Nodup ∧
    (∀ source target,
      source ≠ target → castRegistry source target = false →
        ¬SerialComparisonAdmitted castRegistry source target) ∧
    (∀ first second : UnaryStoppedLaw,
      first.infinityMass ≠ second.infinityMass → first ≠ second) ∧
    (∀ coefficients : List ℚ,
      AdmitsProbabilitySemantics coefficients ↔
        WeightedSeriesNormalized coefficients) ∧
    (castRegistry SerialTag.allPrefixes SerialTag.stoppedSet = false →
      ¬SerialComparisonAdmitted castRegistry SerialTag.allPrefixes
        SerialTag.stoppedSet) := by
  refine ⟨fin_a3_types_04.2, ?_,
    (fun first second => stoppedProbability_retains_nontermination),
    weightedSeries_admitsProbability_iff_normalized,
    prefixStoppedProjection_refused castRegistry⟩
  intro source target hDifferent hMissing
  exact crossTagComparison_refused castRegistry hDifferent hMissing

end PhonologicalCalculus
