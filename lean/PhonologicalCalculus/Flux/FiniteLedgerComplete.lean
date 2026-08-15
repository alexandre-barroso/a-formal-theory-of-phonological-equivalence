import PhonologicalCalculus.Flux.FiniteLedger
import PhonologicalCalculus.Flux.PathWinnerComplete
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Tactic

/-!
# Arbitrary finite-ledger nonidentification

This module isolates the exact finite-dimensional hypotheses supplied by an
analytic periodic audit basis and proves the project-specific consequences:
every ledger with fewer rows than modes has a nonzero analytic periodic
perturbation in its kernel; a sufficiently small nonzero scaling gives a
strictly increasing shift-equivariant gauge; every registered score and every
deterministic consumer of the complete score vector is preserved; and a
held-out point evaluation changes.  The construction is prospective and
ledger-relative: it produces one alternative for each declared finite audit.
-/

namespace PhonologicalCalculus.Flux

open Finset Function Matrix
open scoped BigOperators

noncomputable section

/-- A finite family of analytically and periodically admissible perturbation
modes.  Linear independence is part of the word `basis`; derivative bounds
make the admissible monotonicity scaling explicit. -/
structure AnalyticPeriodicAuditBasis (K : ℕ) where
  period : ℝ
  period_pos : 0 < period
  mode : Fin K → ℝ → ℝ
  modeDeriv : Fin K → ℝ → ℝ
  analytic : ∀ k x, AnalyticAt ℝ (mode k) x
  periodic : ∀ k, Periodic (mode k) period
  hasDeriv : ∀ k x, HasDerivAt (mode k) (modeDeriv k x) x
  derivativeBound : Fin K → ℝ
  derivativeBound_nonneg : ∀ k, 0 ≤ derivativeBound k
  derivative_le : ∀ k x, |modeDeriv k x| ≤ derivativeBound k
  independent : LinearIndependent ℝ mode

/-- Linear synthesis of one perturbation from its finite coefficient vector. -/
def finiteModePerturbation {K : ℕ} (basis : AnalyticPeriodicAuditBasis K)
    (coefficient : Fin K → ℝ) : ℝ → ℝ :=
  fun x => ∑ k, coefficient k * basis.mode k x

/-- The synthesized perturbation is analytic everywhere. -/
theorem finiteModePerturbation_analytic {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) (x : ℝ) :
    AnalyticAt ℝ (finiteModePerturbation basis coefficient) x := by
  unfold finiteModePerturbation
  exact Finset.univ.analyticAt_fun_sum fun k _ => by
    have hscaled : AnalyticAt ℝ (coefficient k • basis.mode k) x :=
      (basis.analytic k x).const_smul
    have heq : (fun y : ℝ => coefficient k * basis.mode k y) =
        coefficient k • basis.mode k := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact hscaled

/-- The synthesized perturbation inherits the declared period. -/
theorem finiteModePerturbation_periodic {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) :
    Periodic (finiteModePerturbation basis coefficient) basis.period := by
  intro x
  simp only [finiteModePerturbation]
  apply Finset.sum_congr rfl
  intro k _
  rw [basis.periodic k x]

/-- Exact derivative of a synthesized finite perturbation. -/
theorem finiteModePerturbation_hasDerivAt {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) (x : ℝ) :
    HasDerivAt (finiteModePerturbation basis coefficient)
      (∑ k, coefficient k * basis.modeDeriv k x) x := by
  unfold finiteModePerturbation
  exact HasDerivAt.fun_sum fun k _ =>
      (basis.hasDeriv k x).const_mul (coefficient k)

/-- The coefficient-weighted derivative bound used by the monotonicity
proof. -/
def finiteModeDerivativeBudget {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) : ℝ :=
  ∑ k, |coefficient k| * basis.derivativeBound k

theorem finiteModeDerivativeBudget_nonneg {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) :
    0 ≤ finiteModeDerivativeBudget basis coefficient := by
  unfold finiteModeDerivativeBudget
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg _) (basis.derivativeBound_nonneg k)

/-- The derivative of the finite perturbation is globally controlled by the
declared coefficient-weighted budget. -/
theorem finiteModePerturbation_deriv_abs_le {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) (x : ℝ) :
    |deriv (finiteModePerturbation basis coefficient) x| ≤
      finiteModeDerivativeBudget basis coefficient := by
  rw [(finiteModePerturbation_hasDerivAt basis coefficient x).deriv]
  calc
    |∑ k, coefficient k * basis.modeDeriv k x| ≤
        ∑ k, |coefficient k * basis.modeDeriv k x| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ k, |coefficient k| * |basis.modeDeriv k x| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul]
    _ ≤ ∑ k, |coefficient k| * basis.derivativeBound k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (basis.derivative_le k x) (abs_nonneg _)
    _ = finiteModeDerivativeBudget basis coefficient := rfl

/-- Linear independence makes synthesis injective. -/
theorem finiteModePerturbation_injective {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) :
    Injective (finiteModePerturbation basis) := by
  intro first second heq
  funext k
  apply basis.independent.eq_coords_of_eq
  funext x
  simpa only [finiteModePerturbation, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using congrFun heq x

/-- The exact finite score matrix induced by a declared family of linear
ledger readers. -/
def finiteAuditMatrix {J K : ℕ} (basis : AnalyticPeriodicAuditBasis K)
    (score : Fin J → ((ℝ → ℝ) →ₗ[ℝ] ℝ)) : Matrix (Fin J) (Fin K) ℝ :=
  fun j k => score j (basis.mode k)

/-- A matrix null vector annihilates every registered score of the synthesized
perturbation. -/
theorem finiteAuditScore_eq_zero_of_mulVec_eq_zero {J K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K)
    (score : Fin J → ((ℝ → ℝ) →ₗ[ℝ] ℝ))
    (coefficient : Fin K → ℝ)
    (hnull : finiteAuditMatrix basis score *ᵥ coefficient = 0) :
    ∀ j, score j (finiteModePerturbation basis coefficient) = 0 := by
  intro j
  have hj := congrFun hnull j
  have hfunction : finiteModePerturbation basis coefficient =
      ∑ k, coefficient k • basis.mode k := by
    funext x
    simp only [finiteModePerturbation, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hfunction, map_sum]
  simp only [LinearMap.map_smul, smul_eq_mul]
  simpa only [finiteAuditMatrix, Matrix.mulVec, dotProduct,
    Pi.zero_apply, mul_comm] using hj

/-- The admissible alternative gauge obtained by adding a scaled periodic
perturbation to the identity. -/
def finiteLedgerGauge {K : ℕ} (basis : AnalyticPeriodicAuditBasis K)
    (coefficient : Fin K → ℝ) (scale x : ℝ) : ℝ :=
  x + scale * finiteModePerturbation basis coefficient x

/-- Every synthesized gauge satisfies the exact load-translation law at its
declared period. -/
theorem finiteLedgerGauge_shiftEquivariant {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ)
    (scale : ℝ) :
    ShiftEquivariant (finiteLedgerGauge basis coefficient scale) basis.period := by
  intro x
  unfold finiteLedgerGauge
  rw [finiteModePerturbation_periodic basis coefficient x]
  ring

/-- The exact derivative of the scaled gauge. -/
theorem finiteLedgerGauge_hasDerivAt {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ)
    (scale x : ℝ) :
    HasDerivAt (finiteLedgerGauge basis coefficient scale)
      (1 + scale * ∑ k, coefficient k * basis.modeDeriv k x) x := by
  have hsum := (finiteModePerturbation_hasDerivAt basis coefficient x).const_mul scale
  unfold finiteLedgerGauge
  exact (hasDerivAt_id' x).add hsum

/-- Any scale whose derivative budget is strictly below one gives a globally
strictly increasing gauge. -/
theorem finiteLedgerGauge_strictMono_of_budget {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ)
    (scale : ℝ)
    (hbudget : |scale| * finiteModeDerivativeBudget basis coefficient < 1) :
    StrictMono (finiteLedgerGauge basis coefficient scale) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(finiteLedgerGauge_hasDerivAt basis coefficient scale x).deriv]
  have hbound := finiteModePerturbation_deriv_abs_le basis coefficient x
  have hscaled :
      |scale * deriv (finiteModePerturbation basis coefficient) x| < 1 := by
    calc
      |scale * deriv (finiteModePerturbation basis coefficient) x| =
          |scale| * |deriv (finiteModePerturbation basis coefficient) x| :=
        abs_mul _ _
      _ ≤ |scale| * finiteModeDerivativeBudget basis coefficient :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      _ < 1 := hbudget
  have hlower : -1 < scale * deriv (finiteModePerturbation basis coefficient) x :=
    (abs_lt.mp hscaled).1
  rw [(finiteModePerturbation_hasDerivAt basis coefficient x).deriv] at hlower
  linarith

/-- A nonzero scale of a nonzero coefficient vector gives a genuinely
distinct gauge. -/
theorem finiteLedgerGauge_ne_identity {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) {coefficient : Fin K → ℝ}
    {scale : ℝ} (hcoefficient : coefficient ≠ 0) (hscale : scale ≠ 0) :
    finiteLedgerGauge basis coefficient scale ≠ id := by
  have hperturbation : finiteModePerturbation basis coefficient ≠ 0 := by
    intro hzero
    apply hcoefficient
    apply finiteModePerturbation_injective basis
    have hzeroZero : finiteModePerturbation basis (0 : Fin K → ℝ) = 0 := by
      funext x
      simp [finiteModePerturbation]
    exact hzero.trans hzeroZero.symm
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hperturbation
  intro hgauge
  have hpoint := congrFun hgauge x
  change x + scale * finiteModePerturbation basis coefficient x = x at hpoint
  have : scale * finiteModePerturbation basis coefficient x = 0 := by linarith
  exact hx (mul_eq_zero.mp this |>.resolve_left hscale)

/-- Every deterministic consumer of a complete registered score vector is
preserved when the perturbation lies in the ledger kernel.  This one lemma
covers winner, harmony, tie, margin, and fixed-support MaxEnt consumers once
their complete score reader is supplied. -/
theorem finiteLedger_all_consumers_preserved {J K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K)
    (score : Fin J → ((ℝ → ℝ) →ₗ[ℝ] ℝ))
    (coefficient : Fin K → ℝ)
    (hnull : finiteAuditMatrix basis score *ᵥ coefficient = 0)
    (baseline : ℝ → ℝ) (scale : ℝ)
    {Answer : Type*} (consumer : (Fin J → ℝ) → Answer) :
    consumer (fun j => score j baseline) =
      consumer (fun j => score j
        (baseline + scale • finiteModePerturbation basis coefficient)) := by
  apply congrArg consumer
  funext j
  rw [map_add, LinearMap.map_smul,
    finiteAuditScore_eq_zero_of_mulVec_eq_zero basis score coefficient hnull j,
    smul_zero, add_zero]

/-- Two nonnegative control quantities can be made simultaneously small by
one positive scalar.  This is the elementary quantitative core of the
arbitrary-closeness clause. -/
theorem exists_positive_scale_for_two_budgets (first second epsilon : ℝ)
    (hfirst : 0 ≤ first) (hsecond : 0 ≤ second) (hepsilon : 0 < epsilon) :
    ∃ scale : ℝ,
      0 < scale ∧ scale * first < 1 ∧ scale * second < epsilon := by
  have hfirstDenom : 0 < first + 1 := by linarith
  have hsecondDenom : 0 < second + 1 := by linarith
  have hfirstBound : 0 < 1 / (first + 1) := one_div_pos.mpr hfirstDenom
  have hsecondBound : 0 < epsilon / (second + 1) :=
    div_pos hepsilon hsecondDenom
  let bound : ℝ := min (1 / (first + 1)) (epsilon / (second + 1))
  have hbound : 0 < bound := by
    exact lt_min hfirstBound hsecondBound
  let scale : ℝ := bound / 2
  have hscale : 0 < scale := div_pos hbound (by norm_num)
  have hscaleLtBound : scale < bound := by
    dsimp [scale]
    linarith
  have hscaleFirst : scale < 1 / (first + 1) :=
    hscaleLtBound.trans_le (min_le_left _ _)
  have hscaleSecond : scale < epsilon / (second + 1) :=
    hscaleLtBound.trans_le (min_le_right _ _)
  refine ⟨scale, hscale, ?_, ?_⟩
  · rcases hfirst.eq_or_lt with rfl | hfirstPos
    · norm_num
    · calc
        scale * first < (1 / (first + 1)) * first :=
          mul_lt_mul_of_pos_right hscaleFirst hfirstPos
        _ = first / (first + 1) := by ring
        _ < 1 := (div_lt_one hfirstDenom).2 (by linarith)
  · rcases hsecond.eq_or_lt with rfl | hsecondPos
    · simpa using hepsilon
    · calc
        scale * second < (epsilon / (second + 1)) * second :=
          mul_lt_mul_of_pos_right hscaleSecond hsecondPos
        _ = (epsilon * second) / (second + 1) := by ring
        _ < epsilon := (div_lt_iff₀ hsecondDenom).2 (by nlinarith)

/-- Total size of the fixed perturbation under a prospectively declared
finite family of seminorms. -/
def finiteAuditSeminormBudget {M K : ℕ}
    (audit : Fin M → Seminorm ℝ (ℝ → ℝ))
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) : ℝ :=
  ∑ r, audit r (finiteModePerturbation basis coefficient)

theorem finiteAuditSeminormBudget_nonneg {M K : ℕ}
    (audit : Fin M → Seminorm ℝ (ℝ → ℝ))
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ) :
    0 ≤ finiteAuditSeminormBudget audit basis coefficient := by
  unfold finiteAuditSeminormBudget
  exact Finset.sum_nonneg fun r _ => apply_nonneg (audit r) _

/-- A positive scale can satisfy the monotonicity condition and make the
gauge perturbation smaller than `epsilon` in every member of any finite,
prospectively declared seminorm family. -/
theorem finiteLedger_exists_scale_arbitrarily_close {M K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ)
    (audit : Fin M → Seminorm ℝ (ℝ → ℝ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ scale : ℝ,
      0 < scale ∧
      |scale| * finiteModeDerivativeBudget basis coefficient < 1 ∧
      ∀ r, audit r (finiteLedgerGauge basis coefficient scale - id) < epsilon := by
  obtain ⟨scale, hscale, hderiv, haudit⟩ :=
    exists_positive_scale_for_two_budgets
      (finiteModeDerivativeBudget basis coefficient)
      (finiteAuditSeminormBudget audit basis coefficient) epsilon
      (finiteModeDerivativeBudget_nonneg basis coefficient)
      (finiteAuditSeminormBudget_nonneg audit basis coefficient) hepsilon
  refine ⟨scale, hscale, ?_, ?_⟩
  · simpa [abs_of_pos hscale] using hderiv
  · intro r
    have hcomponent : audit r (finiteModePerturbation basis coefficient) ≤
        finiteAuditSeminormBudget audit basis coefficient := by
      unfold finiteAuditSeminormBudget
      exact Finset.single_le_sum
        (fun s _ => apply_nonneg (audit s) _) (Finset.mem_univ r)
    have hscaled : audit r
        (scale • finiteModePerturbation basis coefficient) < epsilon := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hscale]
      exact (mul_le_mul_of_nonneg_left hcomponent hscale.le).trans_lt haudit
    have hgaugeDifference :
        finiteLedgerGauge basis coefficient scale - id =
          scale • finiteModePerturbation basis coefficient := by
      funext x
      simp only [finiteLedgerGauge, Pi.sub_apply, Pi.smul_apply, id_eq,
        smul_eq_mul]
      ring
    rw [hgaugeDifference]
    exact hscaled

/-- The finite-ledger gauge transports complete fixed-load path-winner
predicates through the typed KKT bridge. -/
theorem finiteLedgerGauge_completeWinnerPredicates_eq
    {I Candidate : Type*} {K : ℕ}
    (basis : AnalyticPeriodicAuditBasis K) (coefficient : Fin K → ℝ)
    (scale : ℝ)
    (hbudget : |scale| * finiteModeDerivativeBudget basis coefficient < 1)
    (status : Candidate → I → BoxSiteStatus)
    (leftFlux rightFlux : Candidate → I → ℝ)
    (baselineWinner transformedWinner : Candidate → Prop)
    (hbaseline : ExactWinnerKKT baselineWinner
      (baselinePathKKT status leftFlux rightFlux basis.period))
    (htransformed : ExactWinnerKKT transformedWinner
      (transformedPathKKT (finiteLedgerGauge basis coefficient scale)
        status leftFlux rightFlux basis.period)) :
    baselineWinner = transformedWinner := by
  exact fixedLoad_completeWinnerPredicates_eq
    status leftFlux rightFlux basis.period baselineWinner transformedWinner
    hbaseline htransformed
    (finiteLedgerGauge_strictMono_of_budget basis coefficient scale hbudget)
    (finiteLedgerGauge_shiftEquivariant basis coefficient scale)

/-- **FLUX-D3.GENERAL.04.**  For every `J`-row analytic periodic audit and
every strictly larger `K`-mode basis, a nonzero kernel direction exists.  Any
nonzero scaling below the explicit derivative budget is an analytic,
strictly increasing, shift-equivariant, ledger-preserving alternative, while
some held-out point evaluation changes. -/
theorem flux_d3_general_04 {J K : ℕ} (hJK : J < K)
    (basis : AnalyticPeriodicAuditBasis K)
    (score : Fin J → ((ℝ → ℝ) →ₗ[ℝ] ℝ)) :
    ∃ coefficient : Fin K → ℝ,
      coefficient ≠ 0 ∧
      finiteAuditMatrix basis score *ᵥ coefficient = 0 ∧
      ∀ scale : ℝ,
        scale ≠ 0 →
        |scale| * finiteModeDerivativeBudget basis coefficient < 1 →
        (∀ x, AnalyticAt ℝ (finiteLedgerGauge basis coefficient scale) x) ∧
        StrictMono (finiteLedgerGauge basis coefficient scale) ∧
        ShiftEquivariant (finiteLedgerGauge basis coefficient scale)
          basis.period ∧
        finiteLedgerGauge basis coefficient scale ≠ id ∧
        (∀ j, score j (scale • finiteModePerturbation basis coefficient) = 0) ∧
        ∃ x, finiteLedgerGauge basis coefficient scale x ≠ x := by
  obtain ⟨coefficient, hcoefficient, hnull⟩ :=
    finiteLedger_exists_nonzero_nullVector hJK (finiteAuditMatrix basis score)
  refine ⟨coefficient, hcoefficient, hnull, ?_⟩
  intro scale hscale hbudget
  have hdistinct := finiteLedgerGauge_ne_identity basis hcoefficient hscale
  refine ⟨?_, finiteLedgerGauge_strictMono_of_budget basis coefficient scale hbudget,
    finiteLedgerGauge_shiftEquivariant basis coefficient scale,
    hdistinct, ?_, ?_⟩
  · intro x
    unfold finiteLedgerGauge
    have hscaled : AnalyticAt ℝ
        (scale • finiteModePerturbation basis coefficient) x :=
      (finiteModePerturbation_analytic basis coefficient x).const_smul
    have heq : (fun y : ℝ => y + scale * finiteModePerturbation basis coefficient y) =
        id + scale • finiteModePerturbation basis coefficient := by
      funext y
      simp only [Pi.add_apply, Pi.smul_apply, id_eq, smul_eq_mul]
    rw [heq]
    exact analyticAt_id.add hscaled
  · intro j
    rw [LinearMap.map_smul,
      finiteAuditScore_eq_zero_of_mulVec_eq_zero basis score coefficient hnull j,
      smul_zero]
  · exact Function.ne_iff.mp hdistinct

/-- **FLUX-D3.GENERAL.04**, arbitrary-closeness closure.  The same nonzero
ledger-kernel direction admits, for every prospectively declared finite
seminorm audit and every positive tolerance, a nonzero admissible scaling
inside that tolerance.  The resulting alternative retains all structural and
registered-score conclusions of `flux_d3_general_04`. -/
theorem flux_d3_general_04_arbitrarily_close {J K : ℕ} (hJK : J < K)
    (basis : AnalyticPeriodicAuditBasis K)
    (score : Fin J → ((ℝ → ℝ) →ₗ[ℝ] ℝ)) :
    ∃ coefficient : Fin K → ℝ,
      coefficient ≠ 0 ∧
      finiteAuditMatrix basis score *ᵥ coefficient = 0 ∧
      ∀ (M : ℕ) (audit : Fin M → Seminorm ℝ (ℝ → ℝ))
        (epsilon : ℝ),
        0 < epsilon →
        ∃ scale : ℝ,
          scale ≠ 0 ∧
          |scale| * finiteModeDerivativeBudget basis coefficient < 1 ∧
          (∀ r, audit r (finiteLedgerGauge basis coefficient scale - id) < epsilon) ∧
          (∀ x, AnalyticAt ℝ (finiteLedgerGauge basis coefficient scale) x) ∧
          StrictMono (finiteLedgerGauge basis coefficient scale) ∧
          ShiftEquivariant (finiteLedgerGauge basis coefficient scale)
            basis.period ∧
          finiteLedgerGauge basis coefficient scale ≠ id ∧
          (∀ j, score j (scale • finiteModePerturbation basis coefficient) = 0) ∧
          ∃ x, finiteLedgerGauge basis coefficient scale x ≠ x := by
  obtain ⟨coefficient, hcoefficient, hnull⟩ :=
    finiteLedger_exists_nonzero_nullVector hJK (finiteAuditMatrix basis score)
  refine ⟨coefficient, hcoefficient, hnull, ?_⟩
  intro M audit epsilon hepsilon
  obtain ⟨scale, hscale, hbudget, hclose⟩ :=
    finiteLedger_exists_scale_arbitrarily_close
      basis coefficient audit epsilon hepsilon
  have hscaleNe : scale ≠ 0 := ne_of_gt hscale
  have hdistinct := finiteLedgerGauge_ne_identity basis hcoefficient hscaleNe
  refine ⟨scale, hscaleNe, hbudget, hclose, ?_,
    finiteLedgerGauge_strictMono_of_budget basis coefficient scale hbudget,
    finiteLedgerGauge_shiftEquivariant basis coefficient scale,
    hdistinct, ?_, Function.ne_iff.mp hdistinct⟩
  · intro x
    unfold finiteLedgerGauge
    have hscaled : AnalyticAt ℝ
        (scale • finiteModePerturbation basis coefficient) x :=
      (finiteModePerturbation_analytic basis coefficient x).const_smul
    have heq : (fun y : ℝ => y + scale * finiteModePerturbation basis coefficient y) =
        id + scale • finiteModePerturbation basis coefficient := by
      funext y
      simp only [Pi.add_apply, Pi.smul_apply, id_eq, smul_eq_mul]
    rw [heq]
    exact analyticAt_id.add hscaled
  · intro j
    rw [LinearMap.map_smul,
      finiteAuditScore_eq_zero_of_mulVec_eq_zero basis score coefficient hnull j,
      smul_zero]

end

end PhonologicalCalculus.Flux
