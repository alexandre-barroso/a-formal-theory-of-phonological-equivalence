import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer
import PhonologicalCalculus.ContinuousHG.PersistenceAsymptotic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# General-power persistence phases and reach asymptotic

This module closes the exponent-general part of the persistence-phase result.
For a fixed real exponent `p > 1`, it connects the first-zero cell used by the
general-power optimizer to the canonical ratio cell

`A_(K-1)^(p-1) < p * rho <= A_K^(p-1)`

and proves the sharp asymptotic constant for every integer-valued selector
satisfying those cells.  The result is independent of a rounding convention.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped BigOperators Topology

/-- Ascending real-power sum `A_K = sum_{r=1}^K r^q`, with the exponent
`q = 1 / (p - 1)` used by the general-power optimizer. -/
noncomputable def generalPowerSum (p : ℝ) (K : ℕ) : ℝ :=
  ∑ r ∈ Finset.range K,
    (((r + 1 : ℕ) : ℝ) ^ powerShiftExponent p)

theorem generalPowerSum_nonnegative (p : ℝ) (K : ℕ) :
    0 ≤ generalPowerSum p K := by
  unfold generalPowerSum
  exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem generalPowerSum_positive {p : ℝ} {K : ℕ}
    (hK : 0 < K) : 0 < generalPowerSum p K := by
  unfold generalPowerSum
  apply Finset.sum_pos'
  · exact fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  · refine ⟨0, Finset.mem_range.2 hK, ?_⟩
    norm_num

theorem generalPowerSum_monotone (p : ℝ) :
    Monotone (generalPowerSum p) := by
  intro K L hKL
  unfold generalPowerSum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKL)
    (fun r _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Canonical ratio-only phase cell for the real-power path family.  Equality
at the upper boundary belongs to the zero side. -/
def GeneralPowerRatioPhaseCell (p rho : ℝ) (K : ℕ) : Prop :=
  1 < p ∧ 0 < rho ∧ 0 < K ∧
    (generalPowerSum p (K - 1)) ^ (p - 1) < p * rho ∧
    p * rho ≤ (generalPowerSum p K) ^ (p - 1)

/-- The canonical phase inequalities are equivalent to comparison with the
unpowered threshold `(p*rho)^q`. -/
theorem generalPowerRatioPhaseCell_iff_threshold
    {p rho : ℝ} {K : ℕ} :
    GeneralPowerRatioPhaseCell p rho K ↔
      1 < p ∧ 0 < rho ∧ 0 < K ∧
        generalPowerSum p (K - 1) <
          (p * rho) ^ powerShiftExponent p ∧
        (p * rho) ^ powerShiftExponent p ≤ generalPowerSum p K := by
  unfold GeneralPowerRatioPhaseCell powerShiftExponent
  constructor
  · rintro ⟨hp, hrho, hK, hprevious, hboundary⟩
    have hs : 0 < p - 1 := by linarith
    have hprho : 0 ≤ p * rho :=
      (mul_pos (lt_trans zero_lt_one hp) hrho).le
    have hpreviousNonnegative : 0 ≤ generalPowerSum p (K - 1) :=
      generalPowerSum_nonnegative _ _
    have hboundaryNonnegative : 0 ≤ generalPowerSum p K :=
      generalPowerSum_nonnegative _ _
    refine ⟨hp, hrho, hK, ?_, ?_⟩
    · simpa [one_div] using (Real.lt_rpow_inv_iff_of_pos
        hpreviousNonnegative hprho hs).2 hprevious
    · simpa [one_div] using (Real.rpow_inv_le_iff_of_pos
        hprho hboundaryNonnegative hs).2 hboundary
  · rintro ⟨hp, hrho, hK, hprevious, hboundary⟩
    have hs : 0 < p - 1 := by linarith
    have hprho : 0 ≤ p * rho :=
      (mul_pos (lt_trans zero_lt_one hp) hrho).le
    have hpreviousNonnegative : 0 ≤ generalPowerSum p (K - 1) :=
      generalPowerSum_nonnegative _ _
    have hboundaryNonnegative : 0 ≤ generalPowerSum p K :=
      generalPowerSum_nonnegative _ _
    refine ⟨hp, hrho, hK, ?_, ?_⟩
    · exact (Real.lt_rpow_inv_iff_of_pos
        hpreviousNonnegative hprho hs).1 (by simpa [one_div] using hprevious)
    · exact (Real.rpow_inv_le_iff_of_pos
        hprho hboundaryNonnegative hs).1 (by simpa [one_div] using hboundary)

/-- The exact threshold sum used by the optimizer is the ratio threshold
`A_K / (p*rho)^q`. -/
theorem powerPathShiftedSum_eq_ratio
    {h m p : ℝ} (N : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    powerPathShiftedSum h m p N =
      generalPowerSum p N / (p * (h / m)) ^ powerShiftExponent p := by
  rw [powerPathShiftedSum_eq_range]
  change powerPathScale h m p * generalPowerSum p N = _
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hbase : m / (p * h) = (p * (h / m))⁻¹ := by
    field_simp
  have hprho : 0 ≤ p * (h / m) := by positivity
  unfold powerPathScale
  rw [hbase, Real.inv_rpow hprho]
  simp only [div_eq_mul_inv]
  ring

/-- The optimizer's strict/weak first-zero cell is exactly the canonical
general-`p` phase cell in the dimensionless ratio `rho = h/m`. -/
theorem generalPowerFirstZeroCell_iff_ratioPhase
    {h m p : ℝ} {K : ℕ} (hh : 0 < h) (hm : 0 < m) :
    GeneralPowerFirstZeroCell h m p K ↔
      GeneralPowerRatioPhaseCell p (h / m) K := by
  constructor
  · intro hcell
    rcases (generalPowerFirstZeroCell_iff_shiftedSum).1 hcell with
      ⟨hK, _hh, _hm, hp, hprevious, hboundary⟩
    have hrho : 0 < h / m := div_pos hh hm
    apply (generalPowerRatioPhaseCell_iff_threshold).2
    refine ⟨hp, hrho, hK, ?_, ?_⟩
    · rw [powerPathShiftedSum_eq_ratio (K - 1) hh hm hp] at hprevious
      have hden : 0 < (p * (h / m)) ^ powerShiftExponent p := by positivity
      exact (div_lt_one hden).1 hprevious
    · rw [powerPathShiftedSum_eq_ratio K hh hm hp] at hboundary
      have hden : 0 < (p * (h / m)) ^ powerShiftExponent p := by positivity
      exact (one_le_div hden).1 hboundary
  · intro hphase
    rcases (generalPowerRatioPhaseCell_iff_threshold).1 hphase with
      ⟨hp, hrho, hK, hprevious, hboundary⟩
    apply (generalPowerFirstZeroCell_iff_shiftedSum).2
    refine ⟨hK, hh, hm, hp, ?_, ?_⟩
    · rw [powerPathShiftedSum_eq_ratio (K - 1) hh hm hp]
      have hden : 0 < (p * (h / m)) ^ powerShiftExponent p := by positivity
      exact (div_lt_one hden).2 hprevious
    · rw [powerPathShiftedSum_eq_ratio K hh hm hp]
      have hden : 0 < (p * (h / m)) ^ powerShiftExponent p := by positivity
      exact (one_le_div hden).2 hboundary

/-- The ratio phase selects a unique integer first-zero index.  The proof
passes through the general optimizer's strict/weak threshold cell. -/
theorem generalPowerRatioPhaseCell_unique
    {p rho : ℝ} {K L : ℕ}
    (hK : GeneralPowerRatioPhaseCell p rho K)
    (hL : GeneralPowerRatioPhaseCell p rho L) : K = L := by
  have hrho : 0 < rho := hK.2.1
  have firstK : GeneralPowerFirstZeroCell rho 1 p K := by
    apply (generalPowerFirstZeroCell_iff_ratioPhase hrho one_pos).2
    simpa using hK
  have firstL : GeneralPowerFirstZeroCell rho 1 p L := by
    apply (generalPowerFirstZeroCell_iff_ratioPhase hrho one_pos).2
    simpa using hL
  exact generalPowerFirstZeroCell_unique firstK firstL

/-- The first-zero index is nondecreasing in the admitted weight ratio. -/
theorem generalPowerRatioPhaseCell_mono
    {p rhoOne rhoTwo : ℝ} {K L : ℕ}
    (hOne : GeneralPowerRatioPhaseCell p rhoOne K)
    (hTwo : GeneralPowerRatioPhaseCell p rhoTwo L)
    (hrho : rhoOne ≤ rhoTwo) : K ≤ L := by
  rcases (generalPowerRatioPhaseCell_iff_threshold).1 hOne with
    ⟨hp, hrhoOne, hK, hKprevious, _hKboundary⟩
  rcases (generalPowerRatioPhaseCell_iff_threshold).1 hTwo with
    ⟨_hp, _hrhoTwo, _hL, _hLprevious, hLboundary⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 ≤ powerShiftExponent p :=
    (powerShiftExponent_positive hp).le
  have thresholdMono :
      (p * rhoOne) ^ powerShiftExponent p ≤
        (p * rhoTwo) ^ powerShiftExponent p := by
    exact Real.rpow_le_rpow (mul_nonneg hp0.le hrhoOne.le)
      (mul_le_mul_of_nonneg_left hrho hp0.le) hq
  by_contra hnot
  have hLpreviousIndex : L ≤ K - 1 := by omega
  have sumMono : generalPowerSum p L ≤ generalPowerSum p (K - 1) :=
    generalPowerSum_monotone p hLpreviousIndex
  linarith

/-! ## Power-sum bounds -/

/-- Monotone integral comparison gives the two sharp-enough power-sum
bounds used by the persistence asymptotic. -/
theorem generalPowerSum_bounds
    {p : ℝ} (hp : 1 < p) (K : ℕ) :
    ((K : ℝ) ^ (powerShiftExponent p + 1)) /
        (powerShiftExponent p + 1) ≤ generalPowerSum p K ∧
      generalPowerSum p K ≤
        (((K + 1 : ℕ) : ℝ) ^ (powerShiftExponent p + 1)) /
          (powerShiftExponent p + 1) := by
  let q := powerShiftExponent p
  have hq : 0 < q := powerShiftExponent_positive hp
  have hmono : MonotoneOn (fun x : ℝ => x ^ q) (Ici 0) :=
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg hq.le
  constructor
  · have raw := (hmono.mono (by
        intro x hx
        exact hx.1)).integral_le_sum (x₀ := 0) (a := K)
    rw [integral_rpow (Or.inl (by linarith : -1 < q))] at raw
    rw [Real.zero_rpow (by linarith : q + 1 ≠ 0)] at raw
    simpa [generalPowerSum, q] using raw
  · have raw := (hmono.mono (by
        intro x hx
        exact le_trans zero_le_one hx.1)).sum_le_integral (x₀ := 1) (a := K)
    rw [integral_rpow (Or.inl (by linarith : -1 < q))] at raw
    have hden : 0 < q + 1 := by linarith
    have hone : (1 : ℝ) ^ (q + 1) = 1 := Real.one_rpow _
    have upperNonnegative :
        0 ≤ (((K + 1 : ℕ) : ℝ) ^ (q + 1)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have simplified :
        generalPowerSum p K ≤
          ((((K + 1 : ℕ) : ℝ) ^ (q + 1)) - 1) / (q + 1) := by
      simpa [generalPowerSum, q, hone, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using raw
    exact simplified.trans (by
      apply (div_le_div_iff_of_pos_right hden).2
      linarith)

/-! ## Exact phase bounds and the sharp reach scale -/

/-- Continuous comparison scale selected by the power-sum integral bounds. -/
noncomputable def generalPowerReachScale (p rho : ℝ) : ℝ :=
  let q := powerShiftExponent p
  ((q + 1) * (p * rho) ^ q) ^ (1 / (q + 1))

/-- Every canonical phase index lies within one unit of the continuous reach
scale.  This is the exact finite-`rho` estimate behind the asymptotic. -/
theorem generalPowerRatioPhaseCell_reach_bounds
    {p rho : ℝ} {K : ℕ} (hcell : GeneralPowerRatioPhaseCell p rho K) :
    generalPowerReachScale p rho - 1 ≤ (K : ℝ) ∧
      (K : ℝ) < 1 + generalPowerReachScale p rho := by
  rcases (generalPowerRatioPhaseCell_iff_threshold).1 hcell with
    ⟨hp, hrho, hK, hprevious, hboundary⟩
  let q := powerShiftExponent p
  let sigma := q + 1
  let M := (p * rho) ^ q
  have hq : 0 < q := powerShiftExponent_positive hp
  have hsigma : 0 < sigma := by dsimp [sigma]; linarith
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Real.rpow_nonneg (mul_nonneg (le_trans zero_le_one hp.le) hrho.le) _
  have hscaleBase : 0 ≤ sigma * M := mul_nonneg hsigma.le hM
  have hKcast : (((K - 1 : ℕ) : ℝ)) = (K : ℝ) - 1 := by
    have hpred : K - 1 + 1 = K := Nat.sub_add_cancel hK
    have hpredCast : (((K - 1 : ℕ) : ℝ)) + 1 = (K : ℝ) := by
      exact_mod_cast hpred
    linarith
  have hupperSum := (generalPowerSum_bounds hp K).2
  have hlowerSum := (generalPowerSum_bounds hp (K - 1)).1
  change generalPowerSum p (K - 1) < M at hprevious
  change M ≤ generalPowerSum p K at hboundary
  have hrightPower : sigma * M ≤ (((K + 1 : ℕ) : ℝ) ^ sigma) := by
    have := hboundary.trans hupperSum
    apply (le_div_iff₀ hsigma).1 at this
    simpa [mul_comm] using this
  have hleftPower : (((K - 1 : ℕ) : ℝ) ^ sigma) < sigma * M := by
    have := lt_of_le_of_lt hlowerSum hprevious
    apply (div_lt_iff₀ hsigma).1 at this
    simpa [mul_comm] using this
  have hrightBase : 0 ≤ (((K + 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hleftBase : 0 ≤ (((K - 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have lowerRoot :
      (sigma * M) ^ (1 / sigma) ≤ (((K + 1 : ℕ) : ℝ)) := by
    simpa [one_div] using
      ((Real.rpow_inv_le_iff_of_pos hscaleBase hrightBase hsigma).2
        hrightPower)
  have upperRoot :
      (((K - 1 : ℕ) : ℝ)) < (sigma * M) ^ (1 / sigma) := by
    simpa [one_div] using
      ((Real.lt_rpow_inv_iff_of_pos hleftBase hscaleBase hsigma).2
        hleftPower)
  change ((sigma * M) ^ (1 / sigma) - 1 ≤ (K : ℝ)) ∧
    ((K : ℝ) < 1 + (sigma * M) ^ (1 / sigma))
  simp only [one_div] at lowerRoot upperRoot ⊢
  constructor
  · norm_num [Nat.cast_add, Nat.cast_one] at lowerRoot
    linarith
  · rw [hKcast] at upperRoot
    linarith

/-- Fixed-`p` coefficient of the general persistence reach. -/
noncomputable def generalPowerReachCoefficient (p : ℝ) : ℝ :=
  let q := powerShiftExponent p
  ((q + 1) * p ^ q) ^ (1 / (q + 1))

/-- The continuous reach scale separates exactly into a fixed exponent
coefficient and `rho^(1/p)`. -/
theorem generalPowerReachScale_factorization
    {p rho : ℝ} (hp : 1 < p) (hrho : 0 ≤ rho) :
    generalPowerReachScale p rho =
      generalPowerReachCoefficient p * rho ^ (1 / p) := by
  let q := powerShiftExponent p
  let sigma := q + 1
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 < q := powerShiftExponent_positive hp
  have hsigma : 0 < sigma := by dsimp [sigma]; linarith
  have hqSigma : q * (1 / sigma) = 1 / p := by
    have hpm1 : p - 1 ≠ 0 := ne_of_gt (by linarith : 0 < p - 1)
    have hsigmaRaw : 1 / (p - 1) + 1 ≠ 0 := by positivity
    dsimp [q, sigma, powerShiftExponent]
    field_simp [hpm1, ne_of_gt hp0, hsigmaRaw]
    ring
  unfold generalPowerReachScale generalPowerReachCoefficient
  change (sigma * (p * rho) ^ q) ^ (1 / sigma) =
    (sigma * p ^ q) ^ (1 / sigma) * rho ^ (1 / p)
  rw [Real.mul_rpow hp0.le hrho]
  rw [← mul_assoc]
  rw [Real.mul_rpow
    (mul_nonneg hsigma.le (Real.rpow_nonneg hp0.le q))
    (Real.rpow_nonneg hrho q)]
  rw [← Real.rpow_mul hrho q (1 / sigma)]
  rw [hqSigma]

/-- Every integer-valued selector satisfying the exact general-power phase
cell has the sharp reach coefficient.  No closed form or rounding convention
for the selector is assumed. -/
theorem generalPower_phase_index_div_rpow_tendsto_coefficient
    {p : ℝ} (hp : 1 < p) (K : ℝ → ℕ)
    (hphase : ∀ᶠ rho : ℝ in atTop,
      GeneralPowerRatioPhaseCell p rho (K rho)) :
    Tendsto (fun rho : ℝ => (K rho : ℝ) / rho ^ (1 / p))
      atTop (nhds (generalPowerReachCoefficient p)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hexponent : 0 < (1 / p : ℝ) := one_div_pos.mpr hp0
  have hg : Tendsto (fun rho : ℝ => rho ^ (1 / p)) atTop atTop :=
    tendsto_rpow_atTop hexponent
  have hinv : Tendsto (fun rho : ℝ => (rho ^ (1 / p))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hg
  have hlowerLimit : Tendsto
      (fun rho : ℝ => generalPowerReachCoefficient p -
        (rho ^ (1 / p))⁻¹)
      atTop (nhds (generalPowerReachCoefficient p)) := by
    simpa using tendsto_const_nhds.sub hinv
  have hupperLimit : Tendsto
      (fun rho : ℝ => generalPowerReachCoefficient p +
        (rho ^ (1 / p))⁻¹)
      atTop (nhds (generalPowerReachCoefficient p)) := by
    simpa using tendsto_const_nhds.add hinv
  have hbounds : ∀ᶠ rho : ℝ in atTop,
      generalPowerReachCoefficient p - (rho ^ (1 / p))⁻¹ ≤
          (K rho : ℝ) / rho ^ (1 / p) ∧
        (K rho : ℝ) / rho ^ (1 / p) ≤
          generalPowerReachCoefficient p + (rho ^ (1 / p))⁻¹ := by
    filter_upwards [hphase, eventually_gt_atTop (0 : ℝ)] with rho hcell hrho
    have hgpos : 0 < rho ^ (1 / p) := Real.rpow_pos_of_pos hrho _
    have reachFactor := generalPowerReachScale_factorization hp hrho.le
    rcases generalPowerRatioPhaseCell_reach_bounds hcell with
      ⟨hlower, hupper⟩
    rw [reachFactor] at hlower hupper
    constructor
    · apply (le_div_iff₀ hgpos).2
      field_simp [ne_of_gt hgpos]
      nlinarith
    · apply (div_le_iff₀ hgpos).2
      field_simp [ne_of_gt hgpos]
      nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLimit hupperLimit
    (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)

/-- Closed form of the fixed-`p` reach coefficient. -/
theorem generalPowerReachCoefficient_eq_canonical
    {p : ℝ} (hp : 1 < p) :
    generalPowerReachCoefficient p =
      p * (p - 1) ^ (-(p - 1) / p) := by
  let q := powerShiftExponent p
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hs : 0 < p - 1 := by linarith
  have hpm1 : p - 1 ≠ 0 := ne_of_gt hs
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hsigma : q + 1 = p / (p - 1) := by
    dsimp [q, powerShiftExponent]
    field_simp [hpm1]
    ring
  have hr : 1 / (q + 1) = (p - 1) / p := by
    rw [hsigma]
    field_simp [hpm1, hpne]
  have hqr : q * ((p - 1) / p) = 1 / p := by
    dsimp [q, powerShiftExponent]
    field_simp [hpm1, hpne]
  have hrsum : (p - 1) / p + 1 / p = 1 := by
    field_simp [hpne]
    ring
  unfold generalPowerReachCoefficient
  change ((q + 1) * p ^ q) ^ (1 / (q + 1)) = _
  rw [hr, hsigma]
  rw [Real.mul_rpow (div_nonneg hp0.le hs.le)
    (Real.rpow_nonneg hp0.le q)]
  rw [Real.div_rpow hp0.le hs.le]
  rw [← Real.rpow_mul hp0.le q ((p - 1) / p), hqr]
  calc
    p ^ ((p - 1) / p) / (p - 1) ^ ((p - 1) / p) * p ^ (1 / p) =
        (p ^ ((p - 1) / p) * p ^ (1 / p)) /
          (p - 1) ^ ((p - 1) / p) := by ring
    _ = p / (p - 1) ^ ((p - 1) / p) := by
      rw [← Real.rpow_add hp0, hrsum, Real.rpow_one]
    _ = p * (p - 1) ^ (-(p - 1) / p) := by
      have hneg : -(p - 1) / p = -((p - 1) / p) := by ring
      rw [hneg, Real.rpow_neg hs.le]
      ring

/-- Canonical all-`p` persistence asymptotic in its explicit closed form. -/
theorem generalPower_phase_index_div_rpow_tendsto_canonical
    {p : ℝ} (hp : 1 < p) (K : ℝ → ℕ)
    (hphase : ∀ᶠ rho : ℝ in atTop,
      GeneralPowerRatioPhaseCell p rho (K rho)) :
    Tendsto (fun rho : ℝ => (K rho : ℝ) / rho ^ (1 / p))
      atTop (nhds (p * (p - 1) ^ (-(p - 1) / p))) := by
  simpa [generalPowerReachCoefficient_eq_canonical hp] using
    generalPower_phase_index_div_rpow_tendsto_coefficient hp K hphase

/-- Integrated all-`p` CHG-B7 package: common-scale gauge, exact bridge from
the optimizer's first-zero cell to the ratio phase, uniqueness, staircase
monotonicity, and the sharp canonical reach asymptotic. -/
theorem chg_b7_complete_general_power_persistence
    {p : ℝ} (hp : 1 < p) (K : ℝ → ℕ)
    (hphase : ∀ rho : ℝ, 0 < rho →
      GeneralPowerRatioPhaseCell p rho (K rho)) :
    ( ∀ (penalty : ℝ → ℝ) (lambda h m : ℝ), 0 < lambda →
        ∀ x y : List ℝ,
          pathHarmony penalty (lambda * h) (lambda * m) x ≤
              pathHarmony penalty (lambda * h) (lambda * m) y ↔
            pathHarmony penalty h m x ≤ pathHarmony penalty h m y ) ∧
    ( ∀ (h m : ℝ) (L : ℕ), 0 < h → 0 < m →
        (GeneralPowerFirstZeroCell h m p L ↔
          GeneralPowerRatioPhaseCell p (h / m) L) ) ∧
    ( ∀ (rho : ℝ) (L : ℕ), 0 < rho →
        GeneralPowerRatioPhaseCell p rho L → L = K rho ) ∧
    MonotoneOn K (Ioi 0) ∧
    Tendsto (fun rho : ℝ => (K rho : ℝ) / rho ^ (1 / p))
      atTop (nhds (p * (p - 1) ^ (-(p - 1) / p))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro penalty lambda h m hlambda x y
    exact chg_b7_common_scale_preorder penalty hlambda h m x y
  · intro h m L hh hm
    exact generalPowerFirstZeroCell_iff_ratioPhase hh hm
  · intro rho L hrho hL
    exact generalPowerRatioPhaseCell_unique hL (hphase rho hrho)
  · intro rhoOne hrhoOne rhoTwo hrhoTwo hle
    exact generalPowerRatioPhaseCell_mono
      (hphase rhoOne hrhoOne) (hphase rhoTwo hrhoTwo) hle
  · apply generalPower_phase_index_div_rpow_tendsto_canonical hp K
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with rho hrho
    exact hphase rho hrho

end PhonologicalCalculus.ContinuousHG
