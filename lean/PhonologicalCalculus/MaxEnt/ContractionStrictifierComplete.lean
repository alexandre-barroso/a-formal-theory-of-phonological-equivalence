import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Exact contraction-chain strictifier

This module formalizes the project-derived analytic core of
`MAX-G3.CHAIN.02`.  A perturbed quadratic contraction chain is compared with
its exact orbit.  The terminal square is bounded by the exact terminal square
and the sum of squared recurrence residuals.  Combined with any registered
positive compact-cube gap, this converts existence of a zero of a
nonnegative residual objective into existence of a strict negative witness
for a quartic strictifier.

The external semialgebraic minimum-gap theorem and the conventional
complexity classification are deliberately not postulated here.  Concrete
instances supply the gap as an explicit hypothesis.
-/

namespace PhonologicalCalculus.MaxEnt

open Finset
open scoped BigOperators

noncomputable section

/-- Exact orbit of the contraction `x ↦ x²/2`, starting at one. -/
def exactContractionChain : ℕ → ℝ
  | 0 => 1
  | n + 1 => (exactContractionChain n) ^ 2 / 2

@[simp]
theorem exactContractionChain_zero : exactContractionChain 0 = 1 := rfl

@[simp]
theorem exactContractionChain_succ (n : ℕ) :
    exactContractionChain (n + 1) = (exactContractionChain n) ^ 2 / 2 := rfl

/-- The exact contraction orbit stays strictly positive. -/
theorem exactContractionChain_pos (n : ℕ) :
    0 < exactContractionChain n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [exactContractionChain_succ]
      positivity

/-- The exact contraction orbit never exceeds one. -/
theorem exactContractionChain_le_one (n : ℕ) :
    exactContractionChain n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [exactContractionChain_succ]
      have hnonneg := (exactContractionChain_pos n).le
      nlinarith [sq_nonneg (exactContractionChain n - 1)]

/-- Integer-exponent form of the exact orbit. -/
theorem exactContractionChain_zpow (n : ℕ) :
    exactContractionChain n =
      (2 : ℝ) ^ (1 - (2 ^ n : ℕ) : ℤ) := by
  induction n with
  | zero => norm_num [exactContractionChain]
  | succ n ih =>
      rw [exactContractionChain_succ, ih]
      have hsquare (e : ℤ) : ((2 : ℝ) ^ e) ^ 2 =
          (2 : ℝ) ^ (e * 2) := by
        rw [← zpow_natCast, ← zpow_mul]
        norm_num
      rw [hsquare]
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      have hden : (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ) := by norm_num
      nth_rewrite 2 [hden]
      rw [← zpow_sub₀ htwo]
      congr 1
      simp only [pow_succ]
      push_cast
      ring

/-- Closed form of the exact orbit used in the strictifier proof. -/
theorem exactContractionChain_closedForm (n : ℕ) :
    exactContractionChain n = 1 / (2 : ℝ) ^ (2 ^ n - 1) := by
  rw [exactContractionChain_zpow]
  have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hexponent : (1 - (2 ^ n : ℕ) : ℤ) =
      -((2 ^ n - 1 : ℕ) : ℤ) := by omega
  rw [hexponent, zpow_neg, zpow_natCast, one_div]

/-- Dyadic lower bound supplied by the registered compact-cube minimum-gap
theorem. -/
def dyadicCompactGap (bits : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(bits : ℤ))

/-- The explicit chain-length inequality places the exact terminal square
strictly below the dyadic compact-cube gap. -/
theorem exactContractionChain_terminal_lt_dyadicGap
    (m bits : ℕ) (hlength : bits + 3 < 2 ^ (m + 1)) :
    2 * exactContractionChain m ^ 2 < dyadicCompactGap bits := by
  rw [exactContractionChain_zpow]
  unfold dyadicCompactGap
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hidentity :
      2 * ((2 : ℝ) ^ (1 - (2 ^ m : ℕ) : ℤ)) ^ 2 =
        (2 : ℝ) ^ (3 - (2 ^ (m + 1) : ℕ) : ℤ) := by
    have hsquare (e : ℤ) : ((2 : ℝ) ^ e) ^ 2 =
        (2 : ℝ) ^ (e * 2) := by
      rw [← zpow_natCast, ← zpow_mul]
      norm_num
    rw [hsquare]
    have hfactor : (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ) := by norm_num
    nth_rewrite 1 [hfactor]
    rw [← zpow_add₀ htwo]
    congr 1
    simp only [pow_succ]
    push_cast
    ring
  rw [hidentity]
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
  exact_mod_cast (by omega : 3 - (2 ^ (m + 1) : ℕ) < -(bits : ℤ))

/-- Residual of one perturbed contraction step. -/
def contractionResidual (chain : ℕ → ℝ) (i : ℕ) : ℝ :=
  2 * chain (i + 1) - chain i ^ 2

/-- One perturbed contraction step cannot enlarge the previous orbit error
by more than half the absolute recurrence residual. -/
theorem contraction_step_error
    (chain : ℕ → ℝ) (i : ℕ)
    (hchainNonneg : 0 ≤ chain i) (hchainLe : chain i ≤ 1) :
    |chain (i + 1) - exactContractionChain (i + 1)| ≤
      |chain i - exactContractionChain i| +
        |contractionResidual chain i| / 2 := by
  have hexactNonneg := (exactContractionChain_pos i).le
  have hexactLe := exactContractionChain_le_one i
  have hsum : |chain i + exactContractionChain i| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg hchainNonneg hexactNonneg)]
    linarith
  have hfactor :
      |chain i ^ 2 - exactContractionChain i ^ 2| / 2 ≤
        |chain i - exactContractionChain i| := by
    rw [show chain i ^ 2 - exactContractionChain i ^ 2 =
        (chain i - exactContractionChain i) *
          (chain i + exactContractionChain i) by ring,
      abs_mul]
    have hnonneg : 0 ≤ |chain i - exactContractionChain i| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hsum hnonneg]
  have hidentity :
      chain (i + 1) - exactContractionChain (i + 1) =
        (chain i ^ 2 - exactContractionChain i ^ 2) / 2 +
          contractionResidual chain i / 2 := by
    rw [exactContractionChain_succ]
    unfold contractionResidual
    ring
  rw [hidentity]
  calc
    |(chain i ^ 2 - exactContractionChain i ^ 2) / 2 +
        contractionResidual chain i / 2| ≤
        |(chain i ^ 2 - exactContractionChain i ^ 2) / 2| +
          |contractionResidual chain i / 2| := by
      apply (abs_le).2
      constructor
      · linarith [neg_abs_le ((chain i ^ 2 - exactContractionChain i ^ 2) / 2),
          neg_abs_le (contractionResidual chain i / 2)]
      · linarith [le_abs_self ((chain i ^ 2 - exactContractionChain i ^ 2) / 2),
          le_abs_self (contractionResidual chain i / 2)]
    _ = |chain i ^ 2 - exactContractionChain i ^ 2| / 2 +
          |contractionResidual chain i| / 2 := by
      rw [abs_div, abs_div]
      norm_num
    _ ≤ |chain i - exactContractionChain i| +
          |contractionResidual chain i| / 2 :=
      add_le_add hfactor le_rfl

/-- Accumulated terminal error for a chain starting at one. -/
theorem contraction_terminal_error_l1
    (chain : ℕ → ℝ) (m : ℕ)
    (hzero : chain 0 = 1)
    (hcube : ∀ i, i ≤ m → 0 ≤ chain i ∧ chain i ≤ 1) :
    |chain m - exactContractionChain m| ≤
      (1 / 2 : ℝ) *
        (∑ i ∈ Finset.range m, |contractionResidual chain i|) := by
  induction m with
  | zero => simp [hzero]
  | succ m ih =>
      have hprevious := ih (fun i hi => hcube i (Nat.le_trans hi (Nat.le_succ m)))
      have hstep := contraction_step_error chain m
        (hcube m (Nat.le_succ m)).1 (hcube m (Nat.le_succ m)).2
      rw [Finset.sum_range_succ]
      calc
        |chain (m + 1) - exactContractionChain (m + 1)| ≤
            |chain m - exactContractionChain m| +
              |contractionResidual chain m| / 2 := hstep
        _ ≤ (1 / 2 : ℝ) *
              (∑ i ∈ Finset.range m, |contractionResidual chain i|) +
              |contractionResidual chain m| / 2 :=
          add_le_add hprevious le_rfl
        _ = (1 / 2 : ℝ) *
              (∑ i ∈ Finset.range m, |contractionResidual chain i| +
                |contractionResidual chain m|) := by ring

/-- Finite Cauchy--Schwarz bound for the recurrence residual ledger. -/
theorem contraction_residual_l1_sq_le
    (chain : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, |contractionResidual chain i|) ^ 2 ≤
      (m : ℝ) *
        (∑ i ∈ Finset.range m, (contractionResidual chain i) ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.range m) (f := fun i => |contractionResidual chain i|)
  simpa [abs_sq, Finset.card_range] using h

/-- **MAX-G3.CHAIN.02**, terminal-square estimate.  The exact numerical
coefficient is the one used by the registered strictifier. -/
theorem contraction_terminal_square_bound
    (chain : ℕ → ℝ) (m : ℕ)
    (hzero : chain 0 = 1)
    (hcube : ∀ i, i ≤ m → 0 ≤ chain i ∧ chain i ≤ 1) :
    chain m ^ 2 ≤
      2 * exactContractionChain m ^ 2 +
        (m : ℝ) / 2 *
          (∑ i ∈ Finset.range m, (contractionResidual chain i) ^ 2) := by
  have herror := contraction_terminal_error_l1 chain m hzero hcube
  have herrorNonneg : 0 ≤ |chain m - exactContractionChain m| := abs_nonneg _
  have hsumNonneg :
      0 ≤ ∑ i ∈ Finset.range m, |contractionResidual chain i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have herrorSq :
      (chain m - exactContractionChain m) ^ 2 ≤
        (1 / 4 : ℝ) *
          (∑ i ∈ Finset.range m, |contractionResidual chain i|) ^ 2 := by
    rw [← sq_abs (chain m - exactContractionChain m)]
    nlinarith
  have hcauchy := contraction_residual_l1_sq_le chain m
  have hdiffSq :
      2 * (chain m - exactContractionChain m) ^ 2 ≤
        (m : ℝ) / 2 *
          (∑ i ∈ Finset.range m, (contractionResidual chain i) ^ 2) := by
    nlinarith
  have hparallelogram :
      chain m ^ 2 ≤
        2 * exactContractionChain m ^ 2 +
          2 * (chain m - exactContractionChain m) ^ 2 := by
    nlinarith [sq_nonneg (chain m - 2 * exactContractionChain m)]
  linarith

/-- Quartic strictifier built from a nonnegative residual objective and the
contraction-chain recurrence ledger. -/
def contractionStrictifier {U : Type*}
    (residualObjective : U → ℝ) (m : ℕ)
    (u : U) (chain : ℕ → ℝ) : ℝ :=
  2 * residualObjective u +
    (m : ℝ) *
      (∑ i ∈ Finset.range m, (contractionResidual chain i) ^ 2) -
      2 * chain m ^ 2

/-- An exact contraction orbit has zero recurrence residual at every step. -/
theorem exactContractionChain_residual_zero (i : ℕ) :
    contractionResidual exactContractionChain i = 0 := by
  unfold contractionResidual
  rw [exactContractionChain_succ]
  ring

/-- A source zero yields a strict negative strictifier witness on the exact
contraction orbit. -/
theorem contractionStrictifier_negative_of_source_zero
    {U : Type*} (residualObjective : U → ℝ) (m : ℕ) (u : U)
    (hzero : residualObjective u = 0) :
    contractionStrictifier residualObjective m u exactContractionChain < 0 := by
  unfold contractionStrictifier
  simp only [hzero, exactContractionChain_residual_zero, pow_two, mul_zero,
    Finset.sum_const_zero, add_zero]
  nlinarith [exactContractionChain_pos m]

/-- If a nonnegative source objective has a positive global gap whenever it
has no zero, and the exact terminal orbit lies below half that gap, then no
strictifier counterwitness can exist in the source-unsatisfiable case. -/
theorem contractionStrictifier_nonneg_of_gap
    {U : Type*} (domain : U → Prop) (residualObjective : U → ℝ)
    (m : ℕ) (gap : ℝ)
    (hgap : ∀ u, domain u → gap ≤ residualObjective u)
    (hterminal : 2 * exactContractionChain m ^ 2 < gap)
    (u : U) (hu : domain u)
    (chain : ℕ → ℝ) (hchainZero : chain 0 = 1)
    (hchainCube : ∀ i, i ≤ m → 0 ≤ chain i ∧ chain i ≤ 1) :
    0 < contractionStrictifier residualObjective m u chain := by
  have hterminalBound :=
    contraction_terminal_square_bound chain m hchainZero hchainCube
  have hsource := hgap u hu
  unfold contractionStrictifier
  nlinarith

/-- **MAX-G3.CHAIN.02**, exact strictifier equivalence relative to the
registered compact-cube gap.  No complexity-class premise occurs in this
analytic theorem. -/
theorem contractionStrictifier_exists_negative_iff_source_zero
    {U : Type*} (domain : U → Prop) (residualObjective : U → ℝ)
    (m : ℕ) (gap : ℝ)
    (_hresidualNonneg : ∀ u, domain u → 0 ≤ residualObjective u)
    (hgapIfNoZero :
      (¬ ∃ u, domain u ∧ residualObjective u = 0) →
        ∀ u, domain u → gap ≤ residualObjective u)
    (hterminal : 2 * exactContractionChain m ^ 2 < gap) :
    (∃ u, domain u ∧ residualObjective u = 0) ↔
      ∃ u chain,
        domain u ∧ chain 0 = 1 ∧
        (∀ i, i ≤ m → 0 ≤ chain i ∧ chain i ≤ 1) ∧
        contractionStrictifier residualObjective m u chain < 0 := by
  constructor
  · rintro ⟨u, hu, hzero⟩
    refine ⟨u, exactContractionChain, hu, rfl, ?_,
      contractionStrictifier_negative_of_source_zero
        residualObjective m u hzero⟩
    intro i hi
    exact ⟨(exactContractionChain_pos i).le, exactContractionChain_le_one i⟩
  · rintro ⟨u, chain, hu, hzero, hcube, hnegative⟩
    by_contra hsourceNoZero
    have hpositive := contractionStrictifier_nonneg_of_gap
      domain residualObjective m gap (hgapIfNoZero hsourceNoZero)
      hterminal u hu chain hzero hcube
    linarith

/-- **MAX-G3.CHAIN.02**, registered dyadic-gap form.  The source residual
objective is assumed nonnegative on its cube and, in the no-zero case, at
least the inherited dyadic compact minimum.  The project-derived chain length
then yields the exact strict-witness equivalence. -/
theorem max_g3_chain_02
    {U : Type*} (domain : U → Prop) (residualObjective : U → ℝ)
    (m bits : ℕ)
    (hresidualNonneg : ∀ u, domain u → 0 ≤ residualObjective u)
    (hgapIfNoZero :
      (¬ ∃ u, domain u ∧ residualObjective u = 0) →
        ∀ u, domain u → dyadicCompactGap bits ≤ residualObjective u)
    (hlength : bits + 3 < 2 ^ (m + 1)) :
    ((∀ i, 2 * exactContractionChain (i + 1) =
        exactContractionChain i ^ 2) ∧
      2 * exactContractionChain m ^ 2 < dyadicCompactGap bits) ∧
    ((∃ u, domain u ∧ residualObjective u = 0) ↔
      ∃ u chain,
        domain u ∧ chain 0 = 1 ∧
        (∀ i, i ≤ m → 0 ≤ chain i ∧ chain i ≤ 1) ∧
        contractionStrictifier residualObjective m u chain < 0) := by
  have hterminal :=
    exactContractionChain_terminal_lt_dyadicGap m bits hlength
  constructor
  · constructor
    · intro i
      rw [exactContractionChain_succ]
      ring
    · exact hterminal
  · exact contractionStrictifier_exists_negative_iff_source_zero
      domain residualObjective m (dyadicCompactGap bits)
      hresidualNonneg hgapIfNoZero hterminal

end

end PhonologicalCalculus.MaxEnt
