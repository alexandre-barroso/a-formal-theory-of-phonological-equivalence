import PhonologicalCalculus.Flux.PeriodicGauge
import Mathlib.Tactic

/-!
# Complete fixed-load path-winner bridge

This module types the box-constrained KKT language consumed by the fixed-load
path theorem.  A strictly increasing shift-equivariant flux recoding preserves
the admissibility condition at every free, lower-bound, and upper-bound site.
An explicit KKT-to-winner contract then transports that equality to complete
winner predicates.  Complete two-edge free probes recover the shift law.
-/

namespace PhonologicalCalculus.Flux

/-- Location of one coordinate relative to its declared box. -/
inductive BoxSiteStatus
  | lower
  | free
  | upper
  deriving DecidableEq

/-- First-order condition licensed at one box coordinate. -/
def residualAdmissible : BoxSiteStatus → ℝ → Prop
  | .lower, residual => 0 ≤ residual
  | .free, residual => residual = 0
  | .upper, residual => residual ≤ 0

/-- Strict sign preservation entails preservation of every typed box KKT
condition. -/
theorem residualAdmissible_transformed_iff_baseline
    {F : ℝ → ℝ} {lambda y z : ℝ} (status : BoxSiteStatus)
    (hmono : StrictMono F) (hshift : ShiftEquivariant F lambda) :
    residualAdmissible status (transformedResidual F lambda y z) ↔
      residualAdmissible status (baselineResidual lambda y z) := by
  obtain ⟨hnegative, hzero, hpositive⟩ :=
    residual_signs_preserved hmono hshift y z
  cases status with
  | lower =>
      simpa only [residualAdmissible, not_lt] using not_congr hnegative
  | free =>
      exact hzero
  | upper =>
      simpa only [residualAdmissible, not_lt] using not_congr hpositive

/-- Baseline KKT predicate for a finite collection of adjacent path fluxes. -/
def baselinePathKKT {I Candidate : Type*}
    (status : Candidate → I → BoxSiteStatus)
    (leftFlux rightFlux : Candidate → I → ℝ)
    (lambda : ℝ) (candidate : Candidate) : Prop :=
  ∀ site, residualAdmissible (status candidate site)
    (baselineResidual lambda (leftFlux candidate site)
      (rightFlux candidate site))

/-- Transformed KKT predicate for the same finite path contract. -/
def transformedPathKKT {I Candidate : Type*}
    (F : ℝ → ℝ) (status : Candidate → I → BoxSiteStatus)
    (leftFlux rightFlux : Candidate → I → ℝ)
    (lambda : ℝ) (candidate : Candidate) : Prop :=
  ∀ site, residualAdmissible (status candidate site)
    (transformedResidual F lambda (leftFlux candidate site)
      (rightFlux candidate site))

/-- Every candidate satisfies the baseline KKT system exactly when it
satisfies the transformed KKT system. -/
theorem transformedPathKKT_iff_baselinePathKKT
    {I Candidate : Type*} {F : ℝ → ℝ}
    (status : Candidate → I → BoxSiteStatus)
    (leftFlux rightFlux : Candidate → I → ℝ) (lambda : ℝ)
    (hmono : StrictMono F) (hshift : ShiftEquivariant F lambda)
    (candidate : Candidate) :
    transformedPathKKT F status leftFlux rightFlux lambda candidate ↔
      baselinePathKKT status leftFlux rightFlux lambda candidate := by
  constructor <;> intro h site
  · exact (residualAdmissible_transformed_iff_baseline
      (status candidate site) hmono hshift).1 (h site)
  · exact (residualAdmissible_transformed_iff_baseline
      (status candidate site) hmono hshift).2 (h site)

/-- A declared winner predicate is exactly represented by its complete KKT
predicate.  Strict convexity and standard box-KKT sufficiency are supplied by
the concrete objective when this contract is instantiated. -/
def ExactWinnerKKT {Candidate : Type*}
    (winner kkt : Candidate → Prop) : Prop :=
  ∀ candidate, winner candidate ↔ kkt candidate

/-- The complete winner predicates coincide once each objective has its exact
KKT characterization and the flux recoding obeys the fixed-load shift law. -/
theorem fixedLoad_completeWinnerPredicates_eq
    {I Candidate : Type*} {F : ℝ → ℝ}
    (status : Candidate → I → BoxSiteStatus)
    (leftFlux rightFlux : Candidate → I → ℝ) (lambda : ℝ)
    (baselineWinner transformedWinner : Candidate → Prop)
    (hbaseline : ExactWinnerKKT baselineWinner
      (baselinePathKKT status leftFlux rightFlux lambda))
    (htransformed : ExactWinnerKKT transformedWinner
      (transformedPathKKT F status leftFlux rightFlux lambda))
    (hmono : StrictMono F) (hshift : ShiftEquivariant F lambda) :
    baselineWinner = transformedWinner := by
  funext candidate
  apply propext
  rw [hbaseline candidate, htransformed candidate,
    transformedPathKKT_iff_baselinePathKKT
      status leftFlux rightFlux lambda hmono hshift candidate]

/-- Equality of complete free two-edge probe verdicts forces translation
equivariance of the transformed flux. -/
theorem shiftEquivariant_of_completeTwoEdgeProbeEquivalence
    (F : ℝ → ℝ) (lambda : ℝ)
    (hprobe : ∀ y,
      (transformedResidual F lambda y (y + lambda) = 0 ↔
        baselineResidual lambda y (y + lambda) = 0)) :
    ShiftEquivariant F lambda := by
  apply (shiftEquivariant_iff_probe_zeros F lambda).2
  intro y
  exact (hprobe y).2 (by simp [baselineResidual])

/-- The single free-site KKT system whose two adjacent fluxes are `y` and
`y + lambda`.  This is the typed probe used by the necessity direction. -/
def baselineFreeTwoEdgeProbeKKT (lambda y : ℝ) : Unit → Prop :=
  @baselinePathKKT Unit Unit
    (fun _ _ => BoxSiteStatus.free)
    (fun _ _ => y)
    (fun _ _ => y + lambda)
    lambda

/-- Transformed version of the complete single free-site probe. -/
def transformedFreeTwoEdgeProbeKKT (F : ℝ → ℝ) (lambda y : ℝ) :
    Unit → Prop :=
  @transformedPathKKT Unit Unit F
    (fun _ _ => BoxSiteStatus.free)
    (fun _ _ => y)
    (fun _ _ => y + lambda)
    lambda

/-- Equality of the actual winner predicates for every complete free two-edge
probe forces shift equivariance, provided each winner predicate has the
declared exact KKT characterization.  The KKT-to-winner equivalences are
explicit project-specific premises supplied by the concrete objectives; they
are not instances of a generic KKT theorem merely by their name. -/
theorem shiftEquivariant_of_completeFreeProbeWinnerEquivalence
    (F : ℝ → ℝ) (lambda : ℝ)
    (baselineWinner transformedWinner : ℝ → Unit → Prop)
    (hbaseline : ∀ y, ExactWinnerKKT (baselineWinner y)
      (baselineFreeTwoEdgeProbeKKT lambda y))
    (htransformed : ∀ y, ExactWinnerKKT (transformedWinner y)
      (transformedFreeTwoEdgeProbeKKT F lambda y))
    (hwinners : ∀ y, baselineWinner y = transformedWinner y) :
    ShiftEquivariant F lambda := by
  apply (shiftEquivariant_iff_probe_zeros F lambda).2
  intro y
  have hbaselineKKT : baselineFreeTwoEdgeProbeKKT lambda y () := by
    intro site
    cases site
    simp [residualAdmissible, baselineResidual]
  have hbaselineWinner : baselineWinner y () :=
    (hbaseline y ()).2 hbaselineKKT
  have htransformedWinner : transformedWinner y () := by
    rw [← hwinners y]
    exact hbaselineWinner
  have htransformedKKT : transformedFreeTwoEdgeProbeKKT F lambda y () :=
    (htransformed y ()).1 htransformedWinner
  have hsite := htransformedKKT ()
  simpa [transformedFreeTwoEdgeProbeKKT, transformedPathKKT,
    residualAdmissible] using hsite

/-- **FLUX-D1.NECESSITY.04**, typed path-winner closure.  Shift equivariance
plus strict monotonicity is sufficient for complete box-KKT and winner
preservation.  On the unrestricted complete free two-edge probe language,
winner preservation is also sufficient for the shift law. -/
theorem flux_d1_completePathWinnerBridge :
    (∀ {I Candidate : Type*} {F : ℝ → ℝ}
      (status : Candidate → I → BoxSiteStatus)
      (leftFlux rightFlux : Candidate → I → ℝ) (lambda : ℝ)
      (baselineWinner transformedWinner : Candidate → Prop),
      ExactWinnerKKT baselineWinner
          (baselinePathKKT status leftFlux rightFlux lambda) →
      ExactWinnerKKT transformedWinner
          (transformedPathKKT F status leftFlux rightFlux lambda) →
      StrictMono F → ShiftEquivariant F lambda →
      baselineWinner = transformedWinner) ∧
    (∀ (F : ℝ → ℝ) (lambda : ℝ)
      (baselineWinner transformedWinner : ℝ → Unit → Prop),
      (∀ y, ExactWinnerKKT (baselineWinner y)
        (baselineFreeTwoEdgeProbeKKT lambda y)) →
      (∀ y, ExactWinnerKKT (transformedWinner y)
        (transformedFreeTwoEdgeProbeKKT F lambda y)) →
      (∀ y, baselineWinner y = transformedWinner y) →
      ShiftEquivariant F lambda) := by
  constructor
  · intro I Candidate F status leftFlux rightFlux lambda
      baselineWinner transformedWinner hbaseline htransformed hmono hshift
    exact fixedLoad_completeWinnerPredicates_eq
      status leftFlux rightFlux lambda baselineWinner transformedWinner
      hbaseline htransformed hmono hshift
  · exact shiftEquivariant_of_completeFreeProbeWinnerEquivalence

end PhonologicalCalculus.Flux
