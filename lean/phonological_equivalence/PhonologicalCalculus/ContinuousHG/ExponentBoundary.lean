              
import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

namespace PhonologicalCalculus.ContinuousHG

open Set

noncomputable def exponentFaceObjective (p t : ℝ) : ℝ := t ^ p - t

theorem sublinear_rpow_strictly_exceeds_identity
    {p t : ℝ} (hp1 : p < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    t < t ^ p := by
  simpa only [Real.rpow_one] using
    (Real.rpow_lt_rpow_of_exponent_gt ht0 ht1 hp1)

theorem sublinear_exponentFaceObjective_eq_zero_iff
    {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    exponentFaceObjective p t = 0 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro hzero
    by_cases h0 : t = 0
    · exact Or.inl h0
    by_cases h1 : t = 1
    · exact Or.inr h1
    have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
    have ht1' : t < 1 := lt_of_le_of_ne ht1 h1
    have hstrict := sublinear_rpow_strictly_exceeds_identity hp1 ht0' ht1'
    unfold exponentFaceObjective at hzero
    linarith
  · rintro (rfl | rfl)
    · rw [exponentFaceObjective, Real.zero_rpow hp0.ne']
      norm_num
    · simp [exponentFaceObjective]

theorem sublinear_exponentFaceObjective_nonnegative
    {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ exponentFaceObjective p t := by
  by_cases h0 : t = 0
  · subst t
    rw [exponentFaceObjective, Real.zero_rpow hp0.ne']
    norm_num
  by_cases h1 : t = 1
  · subst t
    simp [exponentFaceObjective]
  have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
  have ht1' : t < 1 := lt_of_le_of_ne ht1 h1
  have hstrict := sublinear_rpow_strictly_exceeds_identity hp1 ht0' ht1'
  unfold exponentFaceObjective
  linarith

theorem sublinear_exponentFace_minimizer_iff_endpoint
    {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ s ∈ Icc (0 : ℝ) 1,
      exponentFaceObjective p t ≤ exponentFaceObjective p s) ↔
      t = 0 ∨ t = 1 := by
  constructor
  · intro hmin
    have hle : exponentFaceObjective p t ≤ 0 := by
      simpa [exponentFaceObjective, Real.zero_rpow hp0.ne'] using
        hmin 0 ⟨le_rfl, zero_le_one⟩
    have hnonneg := sublinear_exponentFaceObjective_nonnegative hp0 hp1 ht0 ht1
    have hzero : exponentFaceObjective p t = 0 := le_antisymm hle hnonneg
    exact (sublinear_exponentFaceObjective_eq_zero_iff hp0 hp1 ht0 ht1).mp hzero
  · intro hend s hs
    have hsnonneg :=
      sublinear_exponentFaceObjective_nonnegative hp0 hp1 hs.1 hs.2
    rcases hend with rfl | rfl
    · simpa [exponentFaceObjective, Real.zero_rpow hp0.ne'] using hsnonneg
    · simpa [exponentFaceObjective] using hsnonneg

theorem linear_exponentFace_all_minimizers (t : ℝ) :
    exponentFaceObjective 1 t = 0 := by
  simp [exponentFaceObjective]

theorem sublinear_concentrated_repair_le_split
    {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  exact Real.rpow_add_le_add_rpow ha hb hp0.le hp1.le

theorem linear_repair_distribution_indifferent (a b : ℝ) :
    (a + b) ^ (1 : ℝ) = a ^ (1 : ℝ) + b ^ (1 : ℝ) := by
  simp

theorem superlinear_split_repair_le_concentrated
    {p a b : ℝ} (hp1 : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ p + b ^ p ≤ (a + b) ^ p := by
  exact Real.add_rpow_le_rpow_add ha hb hp1.le

def exponentBoundaryFirstIndex {N : ℕ} (hN : 0 < N) : Fin N := ⟨0, hN⟩

def exponentBoundaryFirstSegment {N : ℕ} (hN : 0 < N) (t : ℝ) : Fin N → ℝ :=
  fun i => if i = exponentBoundaryFirstIndex hN then t else 0

def IsPowerPathMinimizer {N : ℕ} (h m p : ℝ) (d : Fin N → ℝ) : Prop :=
  SolidSimplex d ∧
    ∀ e, SolidSimplex e →
      powerReducedObjective h m p (powerPathWeight N) d ≤
        powerReducedObjective h m p (powerPathWeight N) e

theorem exponentBoundaryFirstSegment_sum {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ∑ i, exponentBoundaryFirstSegment hN t i = t := by
  classical
  rw [Finset.sum_eq_single (exponentBoundaryFirstIndex hN)]
  · simp [exponentBoundaryFirstSegment]
  · intro i _hi hne
    simp [exponentBoundaryFirstSegment, hne]
  · simp

theorem exponentBoundaryFirstSegment_solidSimplex
    {N : ℕ} (hN : 0 < N) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SolidSimplex (exponentBoundaryFirstSegment hN t) := by
  constructor
  · intro i
    simp only [exponentBoundaryFirstSegment]
    split_ifs <;> positivity
  · rw [exponentBoundaryFirstSegment_sum]
    exact ht1

theorem powerPathWeight_firstIndex {N : ℕ} (hN : 0 < N) :
    powerPathWeight N (exponentBoundaryFirstIndex hN) = (N : ℝ) := by
  simp [powerPathWeight, exponentBoundaryFirstIndex]

theorem fin_value_pos_of_ne_exponentBoundaryFirstIndex
    {N : ℕ} (hN : 0 < N) (i : Fin N)
    (hi : i ≠ exponentBoundaryFirstIndex hN) : 0 < i.1 := by
  by_contra hnot
  have hizero : i.1 = 0 := Nat.eq_zero_of_not_pos hnot
  apply hi
  apply Fin.ext
  simpa [exponentBoundaryFirstIndex] using hizero

theorem powerPathWeight_lt_horizon_of_ne_firstIndex
    {N : ℕ} (hN : 0 < N) (i : Fin N)
    (hi : i ≠ exponentBoundaryFirstIndex hN) :
    powerPathWeight N i < (N : ℝ) := by
  unfold powerPathWeight
  exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt i.2)
    (fin_value_pos_of_ne_exponentBoundaryFirstIndex hN i hi)

theorem solidSimplex_coordinate_le_one {N : ℕ} {d : Fin N → ℝ}
    (hd : SolidSimplex d) (i : Fin N) : d i ≤ 1 := by
  have hleSum : d i ≤ ∑ j, d j :=
    Finset.single_le_sum (fun j _ => hd.1 j) (Finset.mem_univ i)
  exact hleSum.trans hd.2

theorem powerPathWeight_gap_nonnegative {N : ℕ} (i : Fin N) :
    0 ≤ (N : ℝ) - powerPathWeight N i := by
  exact sub_nonneg.mpr (powerPathWeight_le_horizon i)

theorem powerPathObjective_exponentBoundary_decomposition
    {N : ℕ} (h m p : ℝ) (d : Fin N → ℝ) :
    powerReducedObjective h m p (powerPathWeight N) d =
      h * ∑ i, (d i ^ p - d i) +
      m * ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) +
      (h - m * (N : ℝ)) * ∑ i, d i := by
  classical
  unfold powerReducedObjective
  calc
    ∑ i, (h * d i ^ p - m * powerPathWeight N i * d i) =
        ∑ i, (h * (d i ^ p - d i) +
          m * (((N : ℝ) - powerPathWeight N i) * d i) +
          (h - m * (N : ℝ)) * d i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = h * ∑ i, (d i ^ p - d i) +
        m * ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) +
        (h - m * (N : ℝ)) * ∑ i, d i := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]

theorem powerPathObjective_firstSegment
    {N : ℕ} (hN : 0 < N) {h m p t : ℝ} (hp : 0 < p) :
    powerReducedObjective h m p (powerPathWeight N)
        (exponentBoundaryFirstSegment hN t) =
      h * t ^ p - m * (N : ℝ) * t := by
  classical
  unfold powerReducedObjective
  rw [Finset.sum_eq_single (exponentBoundaryFirstIndex hN)]
  · simp [exponentBoundaryFirstSegment, powerPathWeight_firstIndex hN]
  · intro i _hi hne
    simp [exponentBoundaryFirstSegment, hne, Real.zero_rpow hp.ne']
  · simp

theorem powerPathObjective_zero {N : ℕ} {h m p : ℝ} (hp : 0 < p) :
    powerReducedObjective h m p (powerPathWeight N) (0 : Fin N → ℝ) = 0 := by
  classical
  simp [powerReducedObjective, Real.zero_rpow hp.ne']

theorem sublinear_powerPathObjective_scalar_lowerBound
    {N : ℕ} {h m p : ℝ} (hh : 0 < h) (hm : 0 < m)
    (hp0 : 0 < p) (hp1 : p < 1) {d : Fin N → ℝ}
    (hd : SolidSimplex d) :
    (h - m * (N : ℝ)) * ∑ i, d i ≤
      powerReducedObjective h m p (powerPathWeight N) d := by
  have hpower : 0 ≤ ∑ i, (d i ^ p - d i) := by
    exact Finset.sum_nonneg fun i _ =>
      sublinear_exponentFaceObjective_nonnegative hp0 hp1
        (hd.1 i) (solidSimplex_coordinate_le_one hd i)
  have hposition :
      0 ≤ ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (powerPathWeight_gap_nonnegative i) (hd.1 i)
  rw [powerPathObjective_exponentBoundary_decomposition]
  nlinarith [mul_nonneg hh.le hpower, mul_nonneg hm.le hposition]

theorem linear_powerPathObjective_decomposition
    {N : ℕ} (h m : ℝ) (d : Fin N → ℝ) :
    powerReducedObjective h m 1 (powerPathWeight N) d =
      m * ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) +
      (h - m * (N : ℝ)) * ∑ i, d i := by
  rw [powerPathObjective_exponentBoundary_decomposition]
  simp

theorem eq_firstSegment_of_weightGap_sum_zero
    {N : ℕ} (hN : 0 < N) {d : Fin N → ℝ} (hd : SolidSimplex d)
    (hgap : ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) = 0) :
    d = exponentBoundaryFirstSegment hN (∑ i, d i) := by
  classical
  have hterm : ∀ i : Fin N,
      ((N : ℝ) - powerPathWeight N i) * d i = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (powerPathWeight_gap_nonnegative j) (hd.1 j))).mp
        hgap i (Finset.mem_univ i)
  have hzero : ∀ i : Fin N, i ≠ exponentBoundaryFirstIndex hN → d i = 0 := by
    intro i hi
    have hpositive : 0 < (N : ℝ) - powerPathWeight N i :=
      sub_pos.mpr (powerPathWeight_lt_horizon_of_ne_firstIndex hN i hi)
    exact (mul_eq_zero.mp (hterm i)).resolve_left hpositive.ne'
  have hsumFirst : (∑ i, d i) = d (exponentBoundaryFirstIndex hN) := by
    rw [Finset.sum_eq_single (exponentBoundaryFirstIndex hN)]
    · intro i _hi hne
      exact hzero i hne
    · simp
  funext i
  by_cases hi : i = exponentBoundaryFirstIndex hN
  · subst i
    simp [exponentBoundaryFirstSegment, hsumFirst]
  · simp [exponentBoundaryFirstSegment, hi, hzero i hi]

theorem firstSegment_eq_zero_iff
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    exponentBoundaryFirstSegment hN t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have := congrFun h (exponentBoundaryFirstIndex hN)
    simpa [exponentBoundaryFirstSegment] using this
  · rintro rfl
    funext i
    simp [exponentBoundaryFirstSegment]

theorem firstSegment_eq_firstVertex_iff
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    exponentBoundaryFirstSegment hN t =
        exponentBoundaryFirstSegment hN 1 ↔ t = 1 := by
  constructor
  · intro h
    have := congrFun h (exponentBoundaryFirstIndex hN)
    simpa [exponentBoundaryFirstSegment] using this
  · rintro rfl
    rfl

theorem zero_mem_solidSimplex (N : ℕ) :
    SolidSimplex (0 : Fin N → ℝ) := by
  constructor <;> simp

theorem linear_powerPathObjective_scalar_lowerBound
    {N : ℕ} {h m : ℝ} (hm : 0 < m) {d : Fin N → ℝ}
    (hd : SolidSimplex d) :
    (h - m * (N : ℝ)) * ∑ i, d i ≤
      powerReducedObjective h m 1 (powerPathWeight N) d := by
  have hposition :
      0 ≤ ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (powerPathWeight_gap_nonnegative i) (hd.1 i)
  rw [linear_powerPathObjective_decomposition]
  nlinarith [mul_nonneg hm.le hposition]

theorem sublinear_powerPath_minimizer_above_iff
    {N : ℕ} (_hN : 0 < N) {h m p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hp0 : 0 < p) (hp1 : p < 1)
    (habove : m * (N : ℝ) < h) (d : Fin N → ℝ) :
    IsPowerPathMinimizer h m p d ↔ d = 0 := by
  constructor
  · rintro ⟨hd, hmin⟩
    have hle := hmin 0 (zero_mem_solidSimplex N)
    rw [powerPathObjective_zero hp0] at hle
    have hlower := sublinear_powerPathObjective_scalar_lowerBound
      hh hm hp0 hp1 hd
    have hsum0 : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd.1 i
    have hsumZero : (∑ i, d i) = 0 := by nlinarith
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hd.1 j)).mp hsumZero i (Finset.mem_univ i)
  · rintro rfl
    refine ⟨zero_mem_solidSimplex N, ?_⟩
    intro e he
    rw [powerPathObjective_zero hp0]
    have hlower := sublinear_powerPathObjective_scalar_lowerBound
      hh hm hp0 hp1 he
    have hsum0 : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he.1 i
    nlinarith

theorem sublinear_powerPath_minimizer_below_iff
    {N : ℕ} (hN : 0 < N) {h m p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hp0 : 0 < p) (hp1 : p < 1)
    (hbelow : h < m * (N : ℝ)) (d : Fin N → ℝ) :
    IsPowerPathMinimizer h m p d ↔
      d = exponentBoundaryFirstSegment hN 1 := by
  let c : ℝ := h - m * (N : ℝ)
  have hc : c < 0 := by dsimp [c]; linarith
  have hvertex : SolidSimplex (exponentBoundaryFirstSegment hN 1) :=
    exponentBoundaryFirstSegment_solidSimplex hN (by norm_num) (by norm_num)
  have hvertexObjective :
      powerReducedObjective h m p (powerPathWeight N)
          (exponentBoundaryFirstSegment hN 1) = c := by
    rw [powerPathObjective_firstSegment hN hp0]
    dsimp [c]
    simp
  constructor
  · rintro ⟨hd, hmin⟩
    have hle := hmin _ hvertex
    rw [hvertexObjective] at hle
    have hlower := sublinear_powerPathObjective_scalar_lowerBound
      hh hm hp0 hp1 hd
    have hsum0 : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd.1 i
    have hsumOne : (∑ i, d i) = 1 := by
      dsimp [c] at hlower hc
      nlinarith [hd.2]
    have hobjective :
        powerReducedObjective h m p (powerPathWeight N) d = c := by
      dsimp [c] at hlower hc ⊢
      nlinarith
    have hpower : 0 ≤ ∑ i, (d i ^ p - d i) := by
      exact Finset.sum_nonneg fun i _ =>
        sublinear_exponentFaceObjective_nonnegative hp0 hp1
          (hd.1 i) (solidSimplex_coordinate_le_one hd i)
    have hposition :
        0 ≤ ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) := by
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (powerPathWeight_gap_nonnegative i) (hd.1 i)
    have hgap :
        ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) = 0 := by
      rw [powerPathObjective_exponentBoundary_decomposition] at hobjective
      dsimp [c] at hobjective
      nlinarith [mul_nonneg hh.le hpower, mul_nonneg hm.le hposition]
    rw [eq_firstSegment_of_weightGap_sum_zero hN hd hgap, hsumOne]
  · rintro rfl
    refine ⟨hvertex, ?_⟩
    intro e he
    rw [hvertexObjective]
    have hlower := sublinear_powerPathObjective_scalar_lowerBound
      hh hm hp0 hp1 he
    have hsum0 : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he.1 i
    dsimp [c] at hlower hc ⊢
    nlinarith [he.2]

theorem sublinear_powerPath_minimizer_equal_iff
    {N : ℕ} (hN : 0 < N) {h m p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hp0 : 0 < p) (hp1 : p < 1)
    (hequal : h = m * (N : ℝ)) (d : Fin N → ℝ) :
    IsPowerPathMinimizer h m p d ↔
      d = 0 ∨ d = exponentBoundaryFirstSegment hN 1 := by
  have hcoeff : h - m * (N : ℝ) = 0 := sub_eq_zero.mpr hequal
  have hzeroObjective := powerPathObjective_zero (N := N) (h := h) (m := m) hp0
  have hvertex : SolidSimplex (exponentBoundaryFirstSegment hN 1) :=
    exponentBoundaryFirstSegment_solidSimplex hN (by norm_num) (by norm_num)
  have hvertexObjective :
      powerReducedObjective h m p (powerPathWeight N)
          (exponentBoundaryFirstSegment hN 1) = 0 := by
    rw [powerPathObjective_firstSegment hN hp0, hequal]
    simp
  constructor
  · rintro ⟨hd, hmin⟩
    have hle := hmin 0 (zero_mem_solidSimplex N)
    rw [hzeroObjective] at hle
    have hlower := sublinear_powerPathObjective_scalar_lowerBound
      hh hm hp0 hp1 hd
    have hlower0 :
        0 ≤ powerReducedObjective h m p (powerPathWeight N) d := by
      rw [hcoeff, zero_mul] at hlower
      exact hlower
    have hobjective :
        powerReducedObjective h m p (powerPathWeight N) d = 0 := by
      linarith
    have hpower : 0 ≤ ∑ i, (d i ^ p - d i) := by
      exact Finset.sum_nonneg fun i _ =>
        sublinear_exponentFaceObjective_nonnegative hp0 hp1
          (hd.1 i) (solidSimplex_coordinate_le_one hd i)
    have hposition :
        0 ≤ ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) := by
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (powerPathWeight_gap_nonnegative i) (hd.1 i)
    have hgap :
        ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) = 0 := by
      rw [powerPathObjective_exponentBoundary_decomposition, hequal] at hobjective
      nlinarith [mul_nonneg hh.le hpower, mul_nonneg hm.le hposition]
    have hsegment := eq_firstSegment_of_weightGap_sum_zero hN hd hgap
    let t : ℝ := ∑ i, d i
    have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => hd.1 i
    have ht1 : t ≤ 1 := hd.2
    have hface : exponentFaceObjective p t = 0 := by
      rw [hsegment] at hobjective
      rw [powerPathObjective_firstSegment hN hp0, hequal] at hobjective
      unfold exponentFaceObjective
      dsimp [t]
      have hmN : 0 < m * (N : ℝ) := by
        have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
        positivity
      nlinarith
    rcases (sublinear_exponentFaceObjective_eq_zero_iff
      hp0 hp1 ht0 ht1).mp hface with ht | ht
    · left
      rw [hsegment]
      exact (firstSegment_eq_zero_iff hN t).2 ht
    · right
      rw [hsegment]
      exact (firstSegment_eq_firstVertex_iff hN t).2 ht
  · rintro (rfl | rfl)
    · refine ⟨zero_mem_solidSimplex N, ?_⟩
      intro e he
      rw [hzeroObjective]
      have hlower := sublinear_powerPathObjective_scalar_lowerBound
        hh hm hp0 hp1 he
      rw [hcoeff, zero_mul] at hlower
      exact hlower
    · refine ⟨hvertex, ?_⟩
      intro e he
      rw [hvertexObjective]
      have hlower := sublinear_powerPathObjective_scalar_lowerBound
        hh hm hp0 hp1 he
      rw [hcoeff, zero_mul] at hlower
      exact hlower

theorem linear_powerPath_minimizer_above_iff
    {N : ℕ} (_hN : 0 < N) {h m : ℝ}
    (hm : 0 < m) (habove : m * (N : ℝ) < h) (d : Fin N → ℝ) :
    IsPowerPathMinimizer h m 1 d ↔ d = 0 := by
  constructor
  · rintro ⟨hd, hmin⟩
    have hle := hmin 0 (zero_mem_solidSimplex N)
    rw [powerPathObjective_zero (p := 1) zero_lt_one] at hle
    have hlower := linear_powerPathObjective_scalar_lowerBound
      (h := h) (m := m) hm hd
    have hsum0 : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd.1 i
    have hsumZero : (∑ i, d i) = 0 := by nlinarith
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hd.1 j)).mp hsumZero i (Finset.mem_univ i)
  · rintro rfl
    refine ⟨zero_mem_solidSimplex N, ?_⟩
    intro e he
    rw [powerPathObjective_zero (p := 1) zero_lt_one]
    have hlower := linear_powerPathObjective_scalar_lowerBound
      (h := h) (m := m) hm he
    have hsum0 : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he.1 i
    nlinarith

theorem linear_powerPath_minimizer_below_iff
    {N : ℕ} (hN : 0 < N) {h m : ℝ}
    (hm : 0 < m) (hbelow : h < m * (N : ℝ)) (d : Fin N → ℝ) :
    IsPowerPathMinimizer h m 1 d ↔
      d = exponentBoundaryFirstSegment hN 1 := by
  let c : ℝ := h - m * (N : ℝ)
  have hc : c < 0 := by dsimp [c]; linarith
  have hvertex : SolidSimplex (exponentBoundaryFirstSegment hN 1) :=
    exponentBoundaryFirstSegment_solidSimplex hN (by norm_num) (by norm_num)
  have hvertexObjective :
      powerReducedObjective h m 1 (powerPathWeight N)
          (exponentBoundaryFirstSegment hN 1) = c := by
    rw [powerPathObjective_firstSegment hN zero_lt_one]
    dsimp [c]
    simp
  constructor
  · rintro ⟨hd, hmin⟩
    have hle := hmin _ hvertex
    rw [hvertexObjective] at hle
    have hlower := linear_powerPathObjective_scalar_lowerBound
      (h := h) (m := m) hm hd
    have hsum0 : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd.1 i
    have hsumOne : (∑ i, d i) = 1 := by
      dsimp [c] at hlower hc
      nlinarith [hd.2]
    have hobjective :
        powerReducedObjective h m 1 (powerPathWeight N) d = c := by
      dsimp [c] at hlower hc ⊢
      nlinarith
    have hposition :
        0 ≤ ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) := by
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (powerPathWeight_gap_nonnegative i) (hd.1 i)
    have hgap :
        ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) = 0 := by
      rw [linear_powerPathObjective_decomposition] at hobjective
      dsimp [c] at hobjective
      nlinarith [mul_nonneg hm.le hposition]
    rw [eq_firstSegment_of_weightGap_sum_zero hN hd hgap, hsumOne]
  · rintro rfl
    refine ⟨hvertex, ?_⟩
    intro e he
    rw [hvertexObjective]
    have hlower := linear_powerPathObjective_scalar_lowerBound
      (h := h) (m := m) hm he
    have hsum0 : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he.1 i
    dsimp [c] at hlower hc ⊢
    nlinarith [he.2]

theorem linear_powerPath_minimizer_equal_iff
    {N : ℕ} (hN : 0 < N) {h m : ℝ}
    (hm : 0 < m) (hequal : h = m * (N : ℝ)) (d : Fin N → ℝ) :
    IsPowerPathMinimizer h m 1 d ↔
      ∃ t ∈ Icc (0 : ℝ) 1, d = exponentBoundaryFirstSegment hN t := by
  have hcoeff : h - m * (N : ℝ) = 0 := sub_eq_zero.mpr hequal
  have hzeroObjective :=
    powerPathObjective_zero (N := N) (h := h) (m := m) (p := 1) zero_lt_one
  constructor
  · rintro ⟨hd, hmin⟩
    have hle := hmin 0 (zero_mem_solidSimplex N)
    rw [hzeroObjective] at hle
    have hlower := linear_powerPathObjective_scalar_lowerBound
      (h := h) (m := m) hm hd
    rw [hcoeff, zero_mul] at hlower
    have hobjective :
        powerReducedObjective h m 1 (powerPathWeight N) d = 0 :=
      le_antisymm hle hlower
    have hposition :
        0 ≤ ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) := by
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (powerPathWeight_gap_nonnegative i) (hd.1 i)
    have hgap :
        ∑ i, (((N : ℝ) - powerPathWeight N i) * d i) = 0 := by
      rw [linear_powerPathObjective_decomposition, hcoeff, zero_mul, add_zero]
        at hobjective
      nlinarith [mul_nonneg hm.le hposition]
    let t : ℝ := ∑ i, d i
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.sum_nonneg fun i _ => hd.1 i
    · exact hd.2
    · exact eq_firstSegment_of_weightGap_sum_zero hN hd hgap
  · rintro ⟨t, ht, rfl⟩
    have hsegment : SolidSimplex (exponentBoundaryFirstSegment hN t) :=
      exponentBoundaryFirstSegment_solidSimplex hN ht.1 ht.2
    have hsegmentObjective :
        powerReducedObjective h m 1 (powerPathWeight N)
            (exponentBoundaryFirstSegment hN t) = 0 := by
      rw [powerPathObjective_firstSegment hN zero_lt_one, hequal]
      simp
    refine ⟨hsegment, ?_⟩
    intro e he
    rw [hsegmentObjective]
    have hlower := linear_powerPathObjective_scalar_lowerBound
      (h := h) (m := m) hm he
    rw [hcoeff, zero_mul] at hlower
    exact hlower

theorem superlinear_finite_equal_distribution_lowerBound
    {N : ℕ} {p : ℝ} (hp : 1 < p) (d : Fin N → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    (∑ i, d i) ^ p ≤
      (N : ℝ) ^ (p - 1) * ∑ i, d i ^ p := by
  simpa using
    (Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := Finset.univ) (f := d) hp.le (by
        intro i _hi
        exact hd i))

theorem chg_b5_full_path_exponent_boundary :
    (∀ (N : ℕ) (_hN : 0 < N) (h m p : ℝ),
      0 < h → 0 < m → 0 < p → p < 1 → m * (N : ℝ) < h →
      ∀ d : Fin N → ℝ, IsPowerPathMinimizer h m p d ↔ d = 0) ∧
    (∀ (N : ℕ) (hN : 0 < N) (h m p : ℝ),
      0 < h → 0 < m → 0 < p → p < 1 → h = m * (N : ℝ) →
      ∀ d : Fin N → ℝ, IsPowerPathMinimizer h m p d ↔
        d = 0 ∨ d = exponentBoundaryFirstSegment hN 1) ∧
    (∀ (N : ℕ) (hN : 0 < N) (h m p : ℝ),
      0 < h → 0 < m → 0 < p → p < 1 → h < m * (N : ℝ) →
      ∀ d : Fin N → ℝ, IsPowerPathMinimizer h m p d ↔
        d = exponentBoundaryFirstSegment hN 1) ∧
    (∀ (N : ℕ) (_hN : 0 < N) (h m : ℝ),
      0 < m → m * (N : ℝ) < h →
      ∀ d : Fin N → ℝ, IsPowerPathMinimizer h m 1 d ↔ d = 0) ∧
    (∀ (N : ℕ) (hN : 0 < N) (h m : ℝ),
      0 < m → h = m * (N : ℝ) →
      ∀ d : Fin N → ℝ, IsPowerPathMinimizer h m 1 d ↔
        ∃ t ∈ Icc (0 : ℝ) 1, d = exponentBoundaryFirstSegment hN t) ∧
    (∀ (N : ℕ) (hN : 0 < N) (h m : ℝ),
      0 < m → h < m * (N : ℝ) →
      ∀ d : Fin N → ℝ, IsPowerPathMinimizer h m 1 d ↔
        d = exponentBoundaryFirstSegment hN 1) ∧
    (∀ (N : ℕ) (p : ℝ), 1 < p → ∀ d : Fin N → ℝ,
      (∀ i, 0 ≤ d i) →
      (∑ i, d i) ^ p ≤
        (N : ℝ) ^ (p - 1) * ∑ i, d i ^ p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N hN h m p hh hm hp0 hp1 habove d
    exact sublinear_powerPath_minimizer_above_iff hN hh hm hp0 hp1 habove d
  · intro N hN h m p hh hm hp0 hp1 hequal d
    exact sublinear_powerPath_minimizer_equal_iff hN hh hm hp0 hp1 hequal d
  · intro N hN h m p hh hm hp0 hp1 hbelow d
    exact sublinear_powerPath_minimizer_below_iff hN hh hm hp0 hp1 hbelow d
  · intro N hN h m hm habove d
    exact linear_powerPath_minimizer_above_iff hN hm habove d
  · intro N hN h m hm hequal d
    exact linear_powerPath_minimizer_equal_iff hN hm hequal d
  · intro N hN h m hm hbelow d
    exact linear_powerPath_minimizer_below_iff hN hm hbelow d
  · intro N p hp d hd
    exact superlinear_finite_equal_distribution_lowerBound hp d hd

theorem chg_b5_complete_exponent_boundary
    {pSub pSup : ℝ}
    (hpSub0 : 0 < pSub) (hpSub1 : pSub < 1) (hpSup1 : 1 < pSup) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((∀ s ∈ Icc (0 : ℝ) 1,
          exponentFaceObjective pSub t ≤ exponentFaceObjective pSub s) ↔
        t = 0 ∨ t = 1)) ∧
    (∀ t : ℝ, exponentFaceObjective 1 t = 0) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a + b) ^ pSub ≤ a ^ pSub + b ^ pSub) ∧
    (∀ a b : ℝ,
      (a + b) ^ (1 : ℝ) = a ^ (1 : ℝ) + b ^ (1 : ℝ)) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a ^ pSup + b ^ pSup ≤ (a + b) ^ pSup) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht0 ht1
    exact sublinear_exponentFace_minimizer_iff_endpoint hpSub0 hpSub1 ht0 ht1
  · exact linear_exponentFace_all_minimizers
  · intro a b ha hb
    exact sublinear_concentrated_repair_le_split hpSub0 hpSub1 ha hb
  · exact linear_repair_distribution_indifferent
  · intro a b ha hb
    exact superlinear_split_repair_le_concentrated hpSup1 ha hb

theorem chg_b5_endpoints_01 :
    (∀ t : ℝ, t ∈ ({0, 1} : Set ℝ) → t = 0 ∨ t = 1) ∧
    (∀ t : ℝ, t ∈ ({0, 1 / 4, 1 / 2, 3 / 4, 1} : Set ℝ) →
      exponentFaceObjective 1 t = 0) := by
  constructor
  · intro t ht
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
  · intro t _
    exact linear_exponentFace_all_minimizers t

theorem chg_b5_repair_02 :
    (4 : ℝ) * ((1 / 4 : ℝ) ^ (2 : ℝ)) < 1 ^ (2 : ℝ) ∧
    (4 : ℝ) * (1 / 4 : ℝ) = 1 ∧
    (4 : ℝ) * (1 / 2 : ℝ) > 1 := by
  norm_num [Real.rpow_two]

end PhonologicalCalculus.ContinuousHG
