import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer
import PhonologicalCalculus.ContinuousHG.PhaseProfile

/-!
# Optimizer-to-phase-profile bridge

This module identifies the normalized shifted-power profile with the unique
finite-dimensional KKT optimizer at a saturated first-zero horizon.  It makes
the phase offset, its uniqueness, the powered-gap law, and active-profile
convexity consequences of the same exact optimizer proof.
-/

namespace PhonologicalCalculus.ContinuousHG

open scoped BigOperators
open Finset Set

/-- For positive exponent and nonempty support, the shifted-power mass is
strictly decreasing in the phase offset on `[0,1)`. -/
theorem shiftedPowerSum_strictAntiOn_Ico
    {q : ℝ} {K : ℕ} (hq : 0 < q) (hK : 0 < K) :
    StrictAntiOn (fun tau : ℝ => shiftedPowerSum q tau K) (Ico 0 1) := by
  intro tauOne hOne tauTwo hTwo hlt
  unfold shiftedPowerSum
  have termStrict : ∀ r ∈ Finset.range K,
      ((((r + 1 : ℕ) : ℝ) - tauTwo) ^ q) <
        ((((r + 1 : ℕ) : ℝ) - tauOne) ^ q) := by
    intro r _hr
    have oneLe : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
    have baseTwoNonnegative :
        0 ≤ ((r + 1 : ℕ) : ℝ) - tauTwo := by
      linarith [hTwo.2]
    apply Real.rpow_lt_rpow baseTwoNonnegative
    · linarith
    · exact hq
  apply Finset.sum_lt_sum (fun r hr => (termStrict r hr).le)
  refine ⟨0, Finset.mem_range.mpr hK, ?_⟩
  exact termStrict 0 (Finset.mem_range.mpr hK)

/-- The phase equation has at most one offset in `[0,1)`. -/
theorem shiftedPowerSum_phaseOffset_unique
    {q target tauOne tauTwo : ℝ} {K : ℕ}
    (hq : 0 < q) (hK : 0 < K)
    (hOne : tauOne ∈ Ico (0 : ℝ) 1)
    (hTwo : tauTwo ∈ Ico (0 : ℝ) 1)
    (heqOne : shiftedPowerSum q tauOne K = target)
    (heqTwo : shiftedPowerSum q tauTwo K = target) :
    tauOne = tauTwo := by
  exact (shiftedPowerSum_strictAntiOn_Ico hq hK).injOn hOne hTwo
    (heqOne.trans heqTwo.symm)

/-- At an active boundary multiplier, reversing the path coordinate exposes
the normalized ascending shifted-power numerator. -/
theorem powerPathDecrease_reverse_eq_shifted_div
    {h m p eta : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (heta : eta < m) (i : Fin K) :
    powerPathDecrease h m p eta K (Fin.rev i) =
      ((((i.1 + 1 : ℕ) : ℝ) - eta / m) ^ powerShiftExponent p) /
        ((p * (h / m)) ^ powerShiftExponent p) := by
  have weightPositive :
      0 < m * powerPathWeight K (Fin.rev i) - eta := by
    rw [powerPathWeight_reverse]
    have oneLe : (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
    nlinarith
  have numeratorNonnegative :
      0 ≤ ((i.1 + 1 : ℕ) : ℝ) - eta / m := by
    have etaDivLtOne : eta / m < 1 := (div_lt_one hm).2 heta
    have oneLe : (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
    linarith
  have denominatorNonnegative : 0 ≤ p * (h / m) := by
    exact (mul_pos (lt_trans zero_lt_one hp) (div_pos hh hm)).le
  have baseIdentity :
      (m * (((i.1 + 1 : ℕ) : ℝ)) - eta) / (p * h) =
        ((((i.1 + 1 : ℕ) : ℝ) - eta / m) /
          (p * (h / m))) := by
    field_simp [ne_of_gt hh, ne_of_gt hm,
      ne_of_gt (lt_trans zero_lt_one hp)]
  unfold powerPathDecrease powerKKTDecrease
  rw [max_eq_left weightPositive.le, powerPathWeight_reverse, baseIdentity,
    Real.div_rpow numeratorNonnegative denominatorNonnegative]

/-- The KKT mass at an active first-zero horizon is exactly the shifted-power
sum divided by its harmony scale. -/
theorem powerPathMass_eq_shiftedPowerSum_div
    {h m p eta : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : eta < m) :
    powerPathMass h m p eta K =
      shiftedPowerSum (powerShiftExponent p) (eta / m) K /
        ((p * (h / m)) ^ powerShiftExponent p) := by
  classical
  unfold powerPathMass powerKKTMass
  calc
    (∑ i : Fin K, powerKKTDecrease h m p eta (powerPathWeight K) i) =
        ∑ i : Fin K,
          powerKKTDecrease h m p eta (powerPathWeight K)
            ((finReverseEquiv K) i) := by
      symm
      exact Equiv.sum_comp (finReverseEquiv K)
        (fun i : Fin K =>
          powerKKTDecrease h m p eta (powerPathWeight K) i)
    _ = ∑ i : Fin K,
        ((((i.1 + 1 : ℕ) : ℝ) - eta / m) ^ powerShiftExponent p) /
          ((p * (h / m)) ^ powerShiftExponent p) := by
      apply Finset.sum_congr rfl
      intro i _
      exact powerPathDecrease_reverse_eq_shifted_div hh hm hp heta i
    _ = (∑ i : Fin K,
        (((i.1 + 1 : ℕ) : ℝ) - eta / m) ^ powerShiftExponent p) /
          ((p * (h / m)) ^ powerShiftExponent p) := by
      rw [Finset.sum_div]
    _ = shiftedPowerSum (powerShiftExponent p) (eta / m) K /
          ((p * (h / m)) ^ powerShiftExponent p) := by
      congr 1
      unfold shiftedPowerSum
      exact Fin.sum_univ_eq_sum_range
        (fun r : ℕ =>
          ((((r + 1 : ℕ) : ℝ) - eta / m) ^ powerShiftExponent p)) K

/-- Unit KKT mass is equivalent to the exact phase equation. -/
theorem powerPathMass_one_iff_phaseEquation
    {h m p eta : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : eta < m) :
    powerPathMass h m p eta K = 1 ↔
      shiftedPowerSum (powerShiftExponent p) (eta / m) K =
        (p * (h / m)) ^ powerShiftExponent p := by
  rw [powerPathMass_eq_shiftedPowerSum_div hh hm hp heta]
  have denominatorPositive :
      0 < (p * (h / m)) ^ powerShiftExponent p := by
    exact Real.rpow_pos_of_pos
      (mul_pos (lt_trans zero_lt_one hp) (div_pos hh hm)) _
  exact div_eq_one_iff_eq (ne_of_gt denominatorPositive)

/-- Every exact first-zero cell determines one and only one normalized phase
offset.  Existence comes from the finite KKT multiplier; uniqueness comes from
strict antitonicity of the shifted-power mass. -/
theorem exists_unique_phaseOffset_of_firstZeroCell
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    ∃! tau : ℝ,
      tau ∈ Ico (0 : ℝ) 1 ∧
      shiftedPowerSum (powerShiftExponent p) tau K =
        (p * (h / m)) ^ powerShiftExponent p := by
  rcases hcell with ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  have restoredCell : GeneralPowerFirstZeroCell h m p K :=
    ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  obtain ⟨eta, heta, _etaUpper, hmass, _hunique⟩ :=
    generalPower_boundary_optimizer_exists restoredCell
  have etaBelowM : eta < m :=
    generalPower_boundary_multiplier_lt_m restoredCell heta hmass
  let tau : ℝ := eta / m
  have tauRange : tau ∈ Ico (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg heta hm.le
    · exact (div_lt_one hm).2 etaBelowM
  have phaseEquation :
      shiftedPowerSum (powerShiftExponent p) tau K =
        (p * (h / m)) ^ powerShiftExponent p := by
    exact (powerPathMass_one_iff_phaseEquation hh hm hp etaBelowM).1 hmass
  refine ⟨tau, ⟨tauRange, phaseEquation⟩, ?_⟩
  intro other hother
  symm
  exact shiftedPowerSum_phaseOffset_unique
    (tauOne := tau) (tauTwo := other)
    (powerShiftExponent_positive hp) hK tauRange hother.1
      phaseEquation hother.2

/-- Under the exact mass equation, every reversed KKT decrease is the
corresponding normalized phase decrease. -/
theorem powerPathDecrease_reverse_eq_normalizedPhaseDecrease
    {h m p eta : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : eta < m)
    (hmass : powerPathMass h m p eta K = 1) (i : Fin K) :
    powerPathDecrease h m p eta K (Fin.rev i) =
      normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K i.1 := by
  rw [powerPathDecrease_reverse_eq_shifted_div hh hm hp heta i]
  unfold normalizedPhaseDecrease
  rw [(powerPathMass_one_iff_phaseEquation hh hm hp heta).1 hmass]

/-- Tail reconstruction of the KKT decrease vector is exactly the normalized
shifted-power phase profile, at every natural index. -/
theorem powerProfileFromDecreases_eq_normalizedPhaseProfile
    {h m p eta : ℝ} {K i : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : eta < m)
    (hmass : powerPathMass h m p eta K = 1) :
    powerProfileFromDecreases (powerPathDecrease h m p eta K) i =
      normalizedPhaseProfile (powerShiftExponent p) (eta / m) K i := by
  classical
  unfold powerProfileFromDecreases
  calc
    (∑ j : Fin K, if i ≤ j.1 then powerPathDecrease h m p eta K j else 0) =
        ∑ r : Fin K,
          if i ≤ (Fin.rev r).1 then
            powerPathDecrease h m p eta K (Fin.rev r) else 0 := by
      symm
      exact Equiv.sum_comp (finReverseEquiv K)
        (fun j : Fin K =>
          if i ≤ j.1 then powerPathDecrease h m p eta K j else 0)
    _ = ∑ r : Fin K,
        if r.1 < K - i then
          normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K r.1
        else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      have conditionIdentity : i ≤ (Fin.rev r).1 ↔ r.1 < K - i := by
        change i ≤ K - (r.1 + 1) ↔ r.1 < K - i
        omega
      by_cases hcondition : i ≤ (Fin.rev r).1
      · have hbefore : r.1 < K - i := conditionIdentity.mp hcondition
        rw [if_pos hcondition, if_pos hbefore]
        exact powerPathDecrease_reverse_eq_normalizedPhaseDecrease
          hh hm hp heta hmass r
      · have hnotBefore : ¬ r.1 < K - i :=
          fun hbefore => hcondition (conditionIdentity.mpr hbefore)
        rw [if_neg hcondition, if_neg hnotBefore]
    _ = ∑ r ∈ Finset.range K,
        if r < K - i then
          normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K r
        else 0 := by
      exact Fin.sum_univ_eq_sum_range
        (fun r : ℕ => if r < K - i then
          normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K r
        else 0) K
    _ = ∑ r ∈ Finset.range (K - i),
          normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K r := by
      calc
        (∑ r ∈ Finset.range K,
          if r < K - i then
            normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K r
          else 0) =
            ∑ r ∈ Finset.range (K - i),
              if r < K - i then
                normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K r
              else 0 := by
          symm
          apply Finset.sum_subset (Finset.range_mono (Nat.sub_le K i))
          intro r hrK hrNotSmall
          have notBefore : ¬ r < K - i := by
            simpa using hrNotSmall
          simp [notBefore]
        _ = ∑ r ∈ Finset.range (K - i),
              normalizedPhaseDecrease (powerShiftExponent p) (eta / m) K r := by
          apply Finset.sum_congr rfl
          intro r hr
          simp [Finset.mem_range.mp hr]
    _ = normalizedPhaseProfile (powerShiftExponent p) (eta / m) K i := by
      unfold normalizedPhaseDecrease normalizedPhaseProfile shiftedPowerSum
      rw [← Finset.sum_div]

/-- The active normalized profile is strictly discretely convex: consecutive
losses strictly decrease until the exact zero boundary. -/
theorem normalizedPhaseProfile_strict_secondDifference_pos
    {q tau : ℝ} {K i : ℕ}
    (hq : 0 < q) (htau : tau < 1) (hden : 0 < shiftedPowerSum q tau K)
    (hi : i + 1 < K) :
    0 < normalizedPhaseProfile q tau K i -
        2 * normalizedPhaseProfile q tau K (i + 1) +
        normalizedPhaseProfile q tau K (i + 2) := by
  have hiK : i < K := lt_trans (Nat.lt_succ_self i) hi
  have nextFormula :=
    normalizedPhaseProfile_sub_succ (q := q) (tau := tau)
      (K := K) (i := i + 1) hi
  have currentFormula :=
    normalizedPhaseProfile_sub_succ (q := q) (tau := tau)
      (K := K) (i := i) hiK
  have predecessorIdentity : K - i = (K - (i + 1)) + 1 := by omega
  have laterBaseNonnegative :
      0 ≤ ((K - (i + 1) : ℕ) : ℝ) - tau := by
    have atLeastOne : 1 ≤ K - (i + 1) := by omega
    have castAtLeastOne : (1 : ℝ) ≤ ((K - (i + 1) : ℕ) : ℝ) := by
      exact_mod_cast atLeastOne
    linarith
  have baseStrict :
      ((K - (i + 1) : ℕ) : ℝ) - tau <
        ((K - i : ℕ) : ℝ) - tau := by
    rw [predecessorIdentity, Nat.cast_add, Nat.cast_one]
    linarith
  have numeratorStrict :
      ((((K - (i + 1) : ℕ) : ℝ) - tau) ^ q) <
        ((((K - i : ℕ) : ℝ) - tau) ^ q) :=
    Real.rpow_lt_rpow laterBaseNonnegative baseStrict hq
  have lossStrict :
      normalizedPhaseProfile q tau K (i + 1) -
          normalizedPhaseProfile q tau K (i + 2) <
        normalizedPhaseProfile q tau K i -
          normalizedPhaseProfile q tau K (i + 1) := by
    rw [nextFormula, currentFormula]
    exact div_lt_div_of_pos_right numeratorStrict hden
  linarith

/-- Complete optimizer/profile package for the registered normalized-phase
theorem.  It supplies the unique offset, the exact KKT-to-profile identity,
the powered-gap law, and strict active discrete convexity. -/
theorem chg_b9_complete_optimizer_phase_profile
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    ∃ eta tau,
      0 ≤ eta ∧ eta < m ∧ tau = eta / m ∧ tau ∈ Ico (0 : ℝ) 1 ∧
      powerPathMass h m p eta K = 1 ∧
      shiftedPowerSum (powerShiftExponent p) tau K =
        (p * (h / m)) ^ powerShiftExponent p ∧
      (∀ other : ℝ,
        other ∈ Ico (0 : ℝ) 1 →
        shiftedPowerSum (powerShiftExponent p) other K =
          (p * (h / m)) ^ powerShiftExponent p → other = tau) ∧
      (∀ i : ℕ,
        powerProfileFromDecreases (powerPathDecrease h m p eta K) i =
          normalizedPhaseProfile (powerShiftExponent p) tau K i) ∧
      (∀ i j : ℕ, i < j → j < K →
        (normalizedProfileLoss (powerShiftExponent p) tau K i) ^ (p - 1) -
          (normalizedProfileLoss (powerShiftExponent p) tau K j) ^ (p - 1) =
            ((j - i : ℕ) : ℝ) / (p * (h / m))) ∧
      (∀ i : ℕ, i + 1 < K →
        0 < normalizedPhaseProfile (powerShiftExponent p) tau K i -
          2 * normalizedPhaseProfile (powerShiftExponent p) tau K (i + 1) +
          normalizedPhaseProfile (powerShiftExponent p) tau K (i + 2)) := by
  rcases hcell with ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  have restoredCell : GeneralPowerFirstZeroCell h m p K :=
    ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  obtain ⟨eta, heta, _etaUpper, hmass, _hunique⟩ :=
    generalPower_boundary_optimizer_exists restoredCell
  have etaBelowM : eta < m :=
    generalPower_boundary_multiplier_lt_m restoredCell heta hmass
  let tau : ℝ := eta / m
  have tauRange : tau ∈ Ico (0 : ℝ) 1 := by
    exact ⟨div_nonneg heta hm.le, (div_lt_one hm).2 etaBelowM⟩
  have phaseEquation :
      shiftedPowerSum (powerShiftExponent p) tau K =
        (p * (h / m)) ^ powerShiftExponent p :=
    (powerPathMass_one_iff_phaseEquation hh hm hp etaBelowM).1 hmass
  have rhoPositive : 0 < h / m := div_pos hh hm
  have phaseDenominatorPositive : 0 < shiftedPowerSum (powerShiftExponent p) tau K := by
    rw [phaseEquation]
    exact Real.rpow_pos_of_pos
      (mul_pos (lt_trans zero_lt_one hp) rhoPositive) _
  refine ⟨eta, tau, heta, etaBelowM, rfl, tauRange, hmass, phaseEquation,
    ?_, ?_, ?_, ?_⟩
  · intro other otherRange otherEquation
    exact (shiftedPowerSum_phaseOffset_unique
      (tauOne := other) (tauTwo := tau)
      (powerShiftExponent_positive hp) hK otherRange tauRange
      otherEquation phaseEquation)
  · intro i
    exact powerProfileFromDecreases_eq_normalizedPhaseProfile
      hh hm hp etaBelowM hmass
  · intro i j hij hjK
    simpa [powerShiftExponent] using
      normalizedProfileLoss_powered_gap
        hp rhoPositive tauRange.1 tauRange.2 hij hjK phaseEquation
  · intro i hi
    exact normalizedPhaseProfile_strict_secondDifference_pos
      (powerShiftExponent_positive hp) tauRange.2
      phaseDenominatorPositive hi

end PhonologicalCalculus.ContinuousHG
