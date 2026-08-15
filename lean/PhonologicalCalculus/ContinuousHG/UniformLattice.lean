import PhonologicalCalculus.ContinuousHG.Quadratic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Uniform-lattice boundary and weight gauge

This module formalizes the exact uniform-lattice comparison used in the
directional power-HG family.  Integer lattice decreases are evaluated against
the all-back profile.  The proof separates the elementary integer-power
inequality, the positional-weight bound, the one-step necessity witness, and
the strict and weak boundary classifications.

The final section records the deterministic common-scale gauge and the
support-resolution algebra that follows from the same boundary.
-/

namespace PhonologicalCalculus.ContinuousHG

open scoped BigOperators

section PowerLemmas

/-- Integer lattice counts satisfy `n^p >= n` for every real exponent
`p >= 1`. -/
theorem natCast_le_rpow_of_one_le (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (n : ℝ) ≤ (n : ℝ) ^ p := by
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  · have hnOne : 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    exact Real.self_le_rpow_of_one_le hnOne hp

/-- For `p > 1`, equality in the integer lattice power inequality occurs
only at counts zero and one. -/
theorem natCast_rpow_eq_iff_zero_or_one (n : ℕ) {p : ℝ} (hp : 1 < p) :
    (n : ℝ) ^ p = (n : ℝ) ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro hequality
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    by_cases hn1 : n = 1
    · exact Or.inr hn1
    have hnTwo : 2 ≤ n := by omega
    have hnCast : 1 < (n : ℝ) := by exact_mod_cast hnTwo
    have hstrict := Real.self_lt_rpow_of_one_lt hnCast hp
    linarith
  · rintro (rfl | rfl)
    · simp [Real.zero_rpow (by linarith : p ≠ 0)]
    · simp

end PowerLemmas

section AbstractLattice

variable {index : Type*} [Fintype index] [DecidableEq index]

/-- Integer decrease counts whose total physical decrease fits inside the
unit activity budget. -/
def UniformLatticeAdmissible (delta : ℝ) (count : index → ℕ) : Prop :=
  delta * ∑ i, (count i : ℝ) ≤ 1

/-- Normalized harmony difference from the all-back profile.  Multiplication
by the positive lattice step gives the original harmony difference. -/
noncomputable def UniformLatticeScore (edgeCoefficient markedness p : ℝ)
    (weight : index → ℝ) (count : index → ℕ) : ℝ :=
  edgeCoefficient * ∑ i, (count i : ℝ) ^ p -
    markedness * ∑ i, weight i * (count i : ℝ)

/-- A single lattice decrease at a designated edge. -/
def singleLatticeCount (first : index) : index → ℕ :=
  fun i => if i = first then 1 else 0

theorem singleLatticeCount_sum (first : index) :
    (∑ i, (singleLatticeCount first i : ℝ)) = 1 := by
  classical
  simp [singleLatticeCount]

theorem singleLatticeCount_power_sum (first : index) {p : ℝ} (hp : 0 < p) :
    (∑ i, (singleLatticeCount first i : ℝ) ^ p) = 1 := by
  classical
  simp [singleLatticeCount, Real.zero_rpow hp.ne']

theorem singleLatticeCount_admissible
    {delta : ℝ} (first : index) (hdelta : delta ≤ 1) :
    UniformLatticeAdmissible delta (singleLatticeCount first) := by
  simp [UniformLatticeAdmissible, singleLatticeCount_sum first, hdelta]

theorem uniformLattice_power_sum_lower
    (count : index → ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, (count i : ℝ)) ≤ ∑ i, (count i : ℝ) ^ p := by
  exact Finset.sum_le_sum fun i _ => natCast_le_rpow_of_one_le (count i) hp

theorem uniformLattice_weighted_sum_upper
    (count : index → ℕ) (weight : index → ℝ) (horizon : ℝ)
    (hweight : ∀ i, weight i ≤ horizon) :
    (∑ i, weight i * (count i : ℝ)) ≤
      horizon * ∑ i, (count i : ℝ) := by
  calc
    (∑ i, weight i * (count i : ℝ)) ≤
        ∑ i, horizon * (count i : ℝ) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hweight i) (Nat.cast_nonneg _)
    _ = horizon * ∑ i, (count i : ℝ) := by
      rw [Finset.mul_sum]

/-- Sufficiency of the uniform-lattice all-back boundary. -/
theorem uniformLatticeScore_nonnegative
    {edgeCoefficient markedness p horizon : ℝ}
    (hedge : markedness * horizon ≤ edgeCoefficient)
    (hmarkedness : 0 ≤ markedness) (hhorizon : 0 ≤ horizon)
    (hp : 1 ≤ p) (weight : index → ℝ)
    (hweight : ∀ i, weight i ≤ horizon) (count : index → ℕ) :
    0 ≤ UniformLatticeScore edgeCoefficient markedness p weight count := by
  have hpower := uniformLattice_power_sum_lower count hp
  have hweighted := uniformLattice_weighted_sum_upper count weight horizon hweight
  have hsum : 0 ≤ ∑ i, (count i : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  unfold UniformLatticeScore
  have hedgeNonnegative : 0 ≤ edgeCoefficient :=
    le_trans (mul_nonneg hmarkedness hhorizon) hedge
  nlinarith [mul_le_mul_of_nonneg_left hpower hedgeNonnegative,
    mul_le_mul_of_nonneg_left hweighted hmarkedness]

/-- Exact score of the one-step necessity witness. -/
theorem uniformLatticeScore_single
    (edgeCoefficient markedness p horizon : ℝ)
    (weight : index → ℝ) (first : index)
    (hp : 0 < p) (hfirst : weight first = horizon) :
    UniformLatticeScore edgeCoefficient markedness p weight
        (singleLatticeCount first) =
      edgeCoefficient - markedness * horizon := by
  classical
  unfold UniformLatticeScore
  rw [singleLatticeCount_power_sum first hp]
  simp [singleLatticeCount, hfirst]

/-- The all-back profile is a weak winner on the complete admitted uniform
lattice exactly at and above the registered boundary. -/
theorem uniformLattice_allBack_weak_iff
    {delta edgeCoefficient markedness p horizon : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hmarkedness : 0 < markedness) (hhorizon : 0 ≤ horizon)
    (hp : 1 ≤ p) (weight : index → ℝ) (first : index)
    (hweight : ∀ i, weight i ≤ horizon)
    (hfirst : weight first = horizon) :
    (∀ count, UniformLatticeAdmissible delta count →
        0 ≤ UniformLatticeScore edgeCoefficient markedness p weight count) ↔
      markedness * horizon ≤ edgeCoefficient := by
  constructor
  · intro hwinner
    have hadmissible := singleLatticeCount_admissible first hdeltaOne
    have hscore := hwinner (singleLatticeCount first) hadmissible
    rw [uniformLatticeScore_single edgeCoefficient markedness p horizon
      weight first (lt_of_lt_of_le zero_lt_one hp) hfirst] at hscore
    linarith
  · intro hboundary count _
    exact uniformLatticeScore_nonnegative hboundary hmarkedness.le hhorizon hp
      weight hweight count

private theorem positive_sum_of_nonzero_count
    {count : index → ℕ} (hcount : count ≠ 0) :
    0 < ∑ i, (count i : ℝ) := by
  classical
  have hexists : ∃ i, count i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hcount (funext hnone)
  rcases hexists with ⟨i, hi⟩
  have hiPositive : 0 < (count i : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hi)
  exact Finset.sum_pos' (fun j _ => Nat.cast_nonneg _)
    ⟨i, Finset.mem_univ i, hiPositive⟩

/-- Strictness of the all-back winner above the boundary. -/
theorem uniformLatticeScore_positive_of_strict_boundary
    {edgeCoefficient markedness p horizon : ℝ}
    (hedge : markedness * horizon < edgeCoefficient)
    (hmarkedness : 0 ≤ markedness) (hhorizon : 0 ≤ horizon)
    (hp : 1 ≤ p) (weight : index → ℝ)
    (hweight : ∀ i, weight i ≤ horizon)
    {count : index → ℕ} (hcount : count ≠ 0) :
    0 < UniformLatticeScore edgeCoefficient markedness p weight count := by
  have hpower := uniformLattice_power_sum_lower count hp
  have hweighted := uniformLattice_weighted_sum_upper count weight horizon hweight
  have hsum := positive_sum_of_nonzero_count hcount
  unfold UniformLatticeScore
  have hedgeNonnegative : 0 ≤ edgeCoefficient := by
    nlinarith [mul_nonneg hmarkedness hhorizon]
  nlinarith [mul_le_mul_of_nonneg_left hpower hedgeNonnegative,
    mul_le_mul_of_nonneg_left hweighted hmarkedness]

/-- The all-back profile is the unique lattice winner exactly above the
boundary. -/
theorem uniformLattice_allBack_unique_iff
    {delta edgeCoefficient markedness p horizon : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hmarkedness : 0 < markedness) (hhorizon : 0 ≤ horizon)
    (hp : 1 ≤ p) (weight : index → ℝ) (first : index)
    (hweight : ∀ i, weight i ≤ horizon)
    (hfirst : weight first = horizon) :
    (∀ count, UniformLatticeAdmissible delta count → count ≠ 0 →
        0 < UniformLatticeScore edgeCoefficient markedness p weight count) ↔
      markedness * horizon < edgeCoefficient := by
  constructor
  · intro hwinner
    have hadmissible := singleLatticeCount_admissible first hdeltaOne
    have hnonzero : singleLatticeCount first ≠ 0 := by
      intro hzero
      have := congrFun hzero first
      simp [singleLatticeCount] at this
    have hscore := hwinner (singleLatticeCount first) hadmissible hnonzero
    rw [uniformLatticeScore_single edgeCoefficient markedness p horizon
      weight first (lt_of_lt_of_le zero_lt_one hp) hfirst] at hscore
    linarith
  · intro hboundary count _ hcount
    exact uniformLatticeScore_positive_of_strict_boundary hboundary
      hmarkedness.le hhorizon hp weight hweight hcount

/-- At a superlinear equality boundary, the complete tie set consists only
of the all-back profile and the one-step decrease on the unique maximal edge. -/
theorem uniformLattice_superlinear_boundary_ties
    {edgeCoefficient markedness p horizon : ℝ}
    (hmarkedness : 0 < markedness) (hhorizon : 0 < horizon) (hp : 1 < p)
    (weight : index → ℝ) (first : index)
    (hweight : ∀ i, weight i ≤ horizon)
    (hfirst : weight first = horizon)
    (hunique : ∀ i, weight i = horizon → i = first)
    (hboundary : edgeCoefficient = markedness * horizon)
    (count : index → ℕ) :
    UniformLatticeScore edgeCoefficient markedness p weight count = 0 ↔
      count = 0 ∨ count = singleLatticeCount first := by
  classical
  let powerGap : ℝ :=
    ∑ i, ((count i : ℝ) ^ p - (count i : ℝ))
  let weightGap : ℝ :=
    ∑ i, (horizon - weight i) * (count i : ℝ)
  have hpowerTerm : ∀ i, 0 ≤ (count i : ℝ) ^ p - (count i : ℝ) := by
    intro i
    exact sub_nonneg.mpr (natCast_le_rpow_of_one_le (count i) hp.le)
  have hweightTerm : ∀ i, 0 ≤ (horizon - weight i) * (count i : ℝ) := by
    intro i
    exact mul_nonneg (sub_nonneg.mpr (hweight i)) (Nat.cast_nonneg _)
  have hpowerGap : 0 ≤ powerGap :=
    Finset.sum_nonneg fun i _ => hpowerTerm i
  have hweightGap : 0 ≤ weightGap :=
    Finset.sum_nonneg fun i _ => hweightTerm i
  have hpowerGapFormula :
      powerGap =
        (∑ i, (count i : ℝ) ^ p) - ∑ i, (count i : ℝ) := by
    unfold powerGap
    rw [Finset.sum_sub_distrib]
  have hweightGapFormula :
      weightGap =
        horizon * (∑ i, (count i : ℝ)) -
          ∑ i, weight i * (count i : ℝ) := by
    unfold weightGap
    calc
      (∑ i, (horizon - weight i) * (count i : ℝ)) =
          ∑ i, (horizon * (count i : ℝ) -
            weight i * (count i : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i, horizon * (count i : ℝ)) -
          ∑ i, weight i * (count i : ℝ) := by
            rw [Finset.sum_sub_distrib]
      _ = horizon * (∑ i, (count i : ℝ)) -
          ∑ i, weight i * (count i : ℝ) := by rw [Finset.mul_sum]
  have hdecomposition :
      UniformLatticeScore edgeCoefficient markedness p weight count =
        markedness * (horizon * powerGap + weightGap) := by
    unfold UniformLatticeScore
    rw [hboundary, hpowerGapFormula, hweightGapFormula]
    ring
  constructor
  · intro hscore
    have htotal : horizon * powerGap + weightGap = 0 := by
      rw [hdecomposition] at hscore
      nlinarith
    have hpowerZero : powerGap = 0 := by nlinarith
    have hweightZero : weightGap = 0 := by nlinarith
    have hpowerPoint :
        ∀ i, (count i : ℝ) ^ p - (count i : ℝ) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => hpowerTerm j)).1 hpowerZero i (Finset.mem_univ i)
    have hweightPoint :
        ∀ i, (horizon - weight i) * (count i : ℝ) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => hweightTerm j)).1 hweightZero i (Finset.mem_univ i)
    have hcoordinate : ∀ i, count i = 0 ∨ count i = 1 ∧ i = first := by
      intro i
      have hpowerEquality : (count i : ℝ) ^ p = (count i : ℝ) := by
        linarith [hpowerPoint i]
      rcases (natCast_rpow_eq_iff_zero_or_one (count i) hp).1 hpowerEquality with
        hzero | hone
      · exact Or.inl hzero
      · right
        refine ⟨hone, ?_⟩
        have hweightEquality := hweightPoint i
        rw [hone] at hweightEquality
        norm_num at hweightEquality
        exact hunique i (by linarith)
    by_cases hfirstCount : count first = 0
    · left
      funext i
      rcases hcoordinate i with hi | ⟨hi, hifirst⟩
      · simp [hi]
      · subst i
        simp [hfirstCount] at hi
    · right
      have hfirstOne : count first = 1 := by
        rcases hcoordinate first with hi | ⟨hi, _⟩
        · exact False.elim (hfirstCount hi)
        · exact hi
      funext i
      by_cases hifirst : i = first
      · subst i
        simp [singleLatticeCount, hfirstOne]
      · rcases hcoordinate i with hi | ⟨_, hi⟩
        · simp [singleLatticeCount, hifirst, hi]
        · exact False.elim (hifirst hi)
  · rintro (rfl | rfl)
    · simp [UniformLatticeScore, Real.zero_rpow (by linarith : p ≠ 0)]
    · rw [uniformLatticeScore_single edgeCoefficient markedness p horizon
        weight first (lt_trans zero_lt_one hp) hfirst]
      exact sub_eq_zero.mpr hboundary

/-- At the linear equality boundary, every admitted multiple of the unique
maximal edge ties and no count on another edge can tie. -/
theorem uniformLattice_linear_boundary_ties
    {edgeCoefficient markedness horizon : ℝ}
    (hmarkedness : 0 < markedness)
    (weight : index → ℝ) (first : index)
    (hweight : ∀ i, weight i ≤ horizon)
    (hfirst : weight first = horizon)
    (hunique : ∀ i, weight i = horizon → i = first)
    (hboundary : edgeCoefficient = markedness * horizon)
    (count : index → ℕ) :
    UniformLatticeScore edgeCoefficient markedness 1 weight count = 0 ↔
      ∀ i, i ≠ first → count i = 0 := by
  classical
  let weightGap : ℝ :=
    ∑ i, (horizon - weight i) * (count i : ℝ)
  have hweightTerm : ∀ i, 0 ≤ (horizon - weight i) * (count i : ℝ) := by
    intro i
    exact mul_nonneg (sub_nonneg.mpr (hweight i)) (Nat.cast_nonneg _)
  have hweightGap : 0 ≤ weightGap :=
    Finset.sum_nonneg fun i _ => hweightTerm i
  have hweightGapFormula :
      weightGap =
        horizon * (∑ i, (count i : ℝ)) -
          ∑ i, weight i * (count i : ℝ) := by
    unfold weightGap
    calc
      (∑ i, (horizon - weight i) * (count i : ℝ)) =
          ∑ i, (horizon * (count i : ℝ) -
            weight i * (count i : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i, horizon * (count i : ℝ)) -
          ∑ i, weight i * (count i : ℝ) := by
            rw [Finset.sum_sub_distrib]
      _ = horizon * (∑ i, (count i : ℝ)) -
          ∑ i, weight i * (count i : ℝ) := by rw [Finset.mul_sum]
  have hdecomposition :
      UniformLatticeScore edgeCoefficient markedness 1 weight count =
        markedness * weightGap := by
    unfold UniformLatticeScore
    rw [hboundary, hweightGapFormula]
    simp_rw [Real.rpow_one]
    ring
  constructor
  · intro hscore i hifirst
    have hgapZero : weightGap = 0 := by
      rw [hdecomposition] at hscore
      nlinarith
    have hpoint : (horizon - weight i) * (count i : ℝ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => hweightTerm j)).1 hgapZero i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hpoint with hweightZero | hcountZero
    · have : weight i = horizon := by linarith
      exact False.elim (hifirst (hunique i this))
    · exact_mod_cast hcountZero
  · intro hsupport
    rw [hdecomposition]
    have hgapZero : weightGap = 0 := by
      unfold weightGap
      apply Finset.sum_eq_zero
      intro i _
      by_cases hifirst : i = first
      · subst i
        simp [hfirst]
      · simp [hsupport i hifirst]
    simp [hgapZero]

end AbstractLattice

section DirectionalPath

/-- The positional weight is nonnegative and never exceeds the horizon. -/
theorem quadraticPathWeight_bounds (N : ℕ) (i : Fin N) :
    0 ≤ quadraticPathWeight N i ∧ quadraticPathWeight N i ≤ (N : ℝ) := by
  constructor
  · exact Nat.cast_nonneg _
  · change (((N - i.1 : ℕ) : ℝ)) ≤ (N : ℝ)
    exact_mod_cast Nat.sub_le N i.1

/-- The first edge is the unique edge with maximal positional weight. -/
theorem quadraticPathWeight_eq_horizon_iff {N : ℕ} (i : Fin N) :
    quadraticPathWeight N i = (N : ℝ) ↔ i.1 = 0 := by
  unfold quadraticPathWeight
  norm_cast
  exact Nat.sub_eq_iff_eq_add (Nat.le_of_lt i.2) |>.trans (by omega)

/-- The directional-family lattice coefficient `h delta^(p-1)`. -/
noncomputable def directionalLatticeCoefficient (h delta p : ℝ) : ℝ :=
  h * delta ^ (p - 1)

/-- Exact registered weak boundary for the complete uniform lattice. -/
theorem chg_b6_allBack_weak_iff
    {N : ℕ} (hN : 0 < N) {h m delta p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) (hp : 1 ≤ p) :
    (∀ count : Fin N → ℕ, UniformLatticeAdmissible delta count →
        0 ≤ UniformLatticeScore (directionalLatticeCoefficient h delta p)
          m p (quadraticPathWeight N) count) ↔
      m * (N : ℝ) ≤ directionalLatticeCoefficient h delta p := by
  let first : Fin N := ⟨0, hN⟩
  apply uniformLattice_allBack_weak_iff hdelta hdeltaOne hm
    (Nat.cast_nonneg N) hp (quadraticPathWeight N) first
  · exact fun i => (quadraticPathWeight_bounds N i).2
  · simp [first, quadraticPathWeight]

/-- Exact registered unique-winner boundary for the complete uniform lattice. -/
theorem chg_b6_allBack_unique_iff
    {N : ℕ} (hN : 0 < N) {h m delta p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) (hp : 1 ≤ p) :
    (∀ count : Fin N → ℕ, UniformLatticeAdmissible delta count →
        count ≠ 0 →
        0 < UniformLatticeScore (directionalLatticeCoefficient h delta p)
          m p (quadraticPathWeight N) count) ↔
      m * (N : ℝ) < directionalLatticeCoefficient h delta p := by
  let first : Fin N := ⟨0, hN⟩
  apply uniformLattice_allBack_unique_iff hdelta hdeltaOne hm
    (Nat.cast_nonneg N) hp (quadraticPathWeight N) first
  · exact fun i => (quadraticPathWeight_bounds N i).2
  · simp [first, quadraticPathWeight]

/-- One-step necessity witness in the original harmony units. -/
theorem chg_b6_oneStep_difference
    {N : ℕ} (hN : 0 < N) (h m delta p : ℝ) (hp : 1 ≤ p) :
    delta * UniformLatticeScore (directionalLatticeCoefficient h delta p)
        m p (quadraticPathWeight N) (singleLatticeCount (⟨0, hN⟩ : Fin N)) =
      delta * (h * delta ^ (p - 1) - m * (N : ℝ)) := by
  rw [uniformLatticeScore_single]
  · rfl
  · linarith
  · simp [quadraticPathWeight]

/-- At the superlinear boundary, the directional path has exactly the
all-back and first-step tie profiles. -/
theorem chg_b6_superlinear_boundary_ties
    {N : ℕ} (hN : 0 < N) {h m delta p : ℝ}
    (hm : 0 < m) (hp : 1 < p)
    (hboundary : directionalLatticeCoefficient h delta p = m * (N : ℝ))
    (count : Fin N → ℕ) :
    UniformLatticeScore (directionalLatticeCoefficient h delta p)
        m p (quadraticPathWeight N) count = 0 ↔
      count = 0 ∨ count = singleLatticeCount (⟨0, hN⟩ : Fin N) := by
  apply uniformLattice_superlinear_boundary_ties hm
    (show 0 < (N : ℝ) by exact_mod_cast hN) hp
    (quadraticPathWeight N) (⟨0, hN⟩ : Fin N)
  · exact fun i => (quadraticPathWeight_bounds N i).2
  · simp [quadraticPathWeight]
  · intro i hi
    exact Fin.ext ((quadraticPathWeight_eq_horizon_iff i).1 hi)
  · simpa [mul_comm] using hboundary

/-- At the linear boundary, precisely the admitted multiples of the first
edge tie the all-back profile. -/
theorem chg_b6_linear_boundary_ties
    {N : ℕ} (hN : 0 < N) {h m delta : ℝ}
    (hm : 0 < m)
    (hboundary : directionalLatticeCoefficient h delta 1 = m * (N : ℝ))
    (count : Fin N → ℕ) :
    UniformLatticeScore (directionalLatticeCoefficient h delta 1)
        m 1 (quadraticPathWeight N) count = 0 ↔
      ∀ i, i ≠ (⟨0, hN⟩ : Fin N) → count i = 0 := by
  apply uniformLattice_linear_boundary_ties hm
    (quadraticPathWeight N) (⟨0, hN⟩ : Fin N)
  · exact fun i => (quadraticPathWeight_bounds N i).2
  · simp [quadraticPathWeight]
  · intro i hi
    exact Fin.ext ((quadraticPathWeight_eq_horizon_iff i).1 hi)
  · simpa [mul_comm] using hboundary

end DirectionalPath

section GaugeAndResolution

/-- Common positive scaling multiplies every complete path harmony by the
same factor. -/
theorem pathHarmony_common_scale
    (penalty : ℝ → ℝ) (lambda h m : ℝ) (profile : List ℝ) :
    pathHarmony penalty (lambda * h) (lambda * m) profile =
      lambda * pathHarmony penalty h m profile := by
  unfold pathHarmony
  ring

/-- Common positive scaling preserves the complete deterministic preorder. -/
theorem chg_b7_common_scale_preorder
    (penalty : ℝ → ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (h m : ℝ) (x y : List ℝ) :
    pathHarmony penalty (lambda * h) (lambda * m) x ≤
        pathHarmony penalty (lambda * h) (lambda * m) y ↔
      pathHarmony penalty h m x ≤ pathHarmony penalty h m y := by
  rw [pathHarmony_common_scale, pathHarmony_common_scale]
  exact mul_le_mul_iff_of_pos_left hlambda

/-- Dimensionless support-resolution ratio. -/
noncomputable def supportResolutionRatio
    (N : ℕ) (h m delta p : ℝ) : ℝ :=
  (N : ℝ) * m / (h * delta ^ (p - 1))

/-- The weak lattice boundary is exactly the ratio inequality `R <= 1`. -/
theorem chg_b8_weak_ratio_iff
    {N : ℕ} {h m delta p : ℝ}
    (hh : 0 < h) (hdelta : 0 < delta) :
    (m * (N : ℝ) ≤ h * delta ^ (p - 1)) ↔
      supportResolutionRatio N h m delta p ≤ 1 := by
  have hpower : 0 < delta ^ (p - 1) := Real.rpow_pos_of_pos hdelta _
  unfold supportResolutionRatio
  rw [div_le_one (mul_pos hh hpower)]
  ring_nf

/-- The strict lattice boundary is exactly the ratio inequality `R < 1`. -/
theorem chg_b8_strict_ratio_iff
    {N : ℕ} {h m delta p : ℝ}
    (hh : 0 < h) (hdelta : 0 < delta) :
    (m * (N : ℝ) < h * delta ^ (p - 1)) ↔
      supportResolutionRatio N h m delta p < 1 := by
  have hpower : 0 < delta ^ (p - 1) := Real.rpow_pos_of_pos hdelta _
  unfold supportResolutionRatio
  rw [div_lt_one (mul_pos hh hpower)]
  ring_nf

/-- Weight-and-resolution capacity used in the horizon formulas. -/
noncomputable def supportResolutionCapacity (h m delta p : ℝ) : ℝ :=
  h * delta ^ (p - 1) / m

/-- Critical uniform-lattice mesh for the weak all-back boundary. -/
noncomputable def criticalSupportMesh
    (N : ℕ) (h m p : ℝ) : ℝ :=
  (m * (N : ℝ) / h) ^ (p - 1)⁻¹

/-- Solving the weak lattice boundary for the mesh gives the exact critical
mesh, with equality retained on the weak, nonunique side. -/
theorem chg_b8_weak_critical_mesh_iff
    {N : ℕ} (hN : 0 < N) {h m delta p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hdelta : 0 < delta) (hp : 1 < p) :
    m * (N : ℝ) ≤ h * delta ^ (p - 1) ↔
      criticalSupportMesh N h m p ≤ delta := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : 0 ≤ m * (N : ℝ) / h := by positivity
  have hexponent : 0 < p - 1 := by linarith
  unfold criticalSupportMesh
  rw [Real.rpow_inv_le_iff_of_pos hratio hdelta.le hexponent]
  constructor
  · intro hboundary
    exact (div_le_iff₀ hh).2 (by simpa [mul_comm] using hboundary)
  · intro hboundary
    have hresult := (div_le_iff₀ hh).1 hboundary
    simpa [mul_comm] using hresult

/-- Refining below the critical mesh is exactly the strict side on which the
all-back profile ceases to be a lattice winner. -/
theorem chg_b8_below_critical_mesh_iff
    {N : ℕ} (hN : 0 < N) {h m delta p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hdelta : 0 < delta) (hp : 1 < p) :
    delta < criticalSupportMesh N h m p ↔
      h * delta ^ (p - 1) < m * (N : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : 0 ≤ m * (N : ℝ) / h := by positivity
  have hexponent : 0 < p - 1 := by linarith
  unfold criticalSupportMesh
  rw [Real.lt_rpow_inv_iff_of_pos hdelta.le hratio hexponent]
  constructor
  · intro hboundary
    have hresult := (lt_div_iff₀ hh).1 hboundary
    simpa [mul_comm] using hresult
  · intro hboundary
    exact (lt_div_iff₀ hh).2 (by simpa [mul_comm] using hboundary)

/-- The weak maximum horizon is the natural floor of the capacity. -/
theorem chg_b8_weak_horizon_iff
    {N : ℕ} {h m delta p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hdelta : 0 < delta) :
    m * (N : ℝ) ≤ h * delta ^ (p - 1) ↔
      N ≤ Nat.floor (supportResolutionCapacity h m delta p) := by
  have hpower : 0 < delta ^ (p - 1) := Real.rpow_pos_of_pos hdelta _
  have hcapacity : 0 ≤ supportResolutionCapacity h m delta p := by
    exact (div_nonneg (mul_nonneg hh.le hpower.le) hm.le)
  rw [← Nat.cast_le (α := ℝ)]
  constructor
  · intro hboundary
    exact_mod_cast Nat.le_floor (show (N : ℝ) ≤
      supportResolutionCapacity h m delta p by
        unfold supportResolutionCapacity
        exact (le_div_iff₀ hm).2 (by simpa [mul_comm] using hboundary))
  · intro hfloor
    have hfloorReal : ((Nat.floor (supportResolutionCapacity h m delta p) : ℕ) : ℝ) ≤
        supportResolutionCapacity h m delta p := Nat.floor_le hcapacity
    have hNcap : (N : ℝ) ≤ supportResolutionCapacity h m delta p :=
      le_trans hfloor hfloorReal
    have hresult := (le_div_iff₀ hm).1 hNcap
    simpa [mul_comm] using hresult

/-- The strict maximum horizon is one less than the natural ceiling of the
capacity; equality remains outside the unique-winner side. -/
theorem chg_b8_strict_horizon_iff
    {N : ℕ} {h m delta p : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hdelta : 0 < delta) :
    m * (N : ℝ) < h * delta ^ (p - 1) ↔
      N ≤ Nat.ceil (supportResolutionCapacity h m delta p) - 1 := by
  have hpower : 0 < delta ^ (p - 1) := Real.rpow_pos_of_pos hdelta _
  have hcapacity : 0 < supportResolutionCapacity h m delta p := by
    exact div_pos (mul_pos hh hpower) hm
  have hceil : 0 < Nat.ceil (supportResolutionCapacity h m delta p) :=
    Nat.ceil_pos.mpr hcapacity
  rw [Nat.le_sub_one_iff_lt hceil, Nat.lt_ceil]
  unfold supportResolutionCapacity
  constructor
  · intro hboundary
    have hresult := (lt_div_iff₀ hm).2 (by simpa [mul_comm] using hboundary)
    exact hresult
  · intro hboundary
    have hresult := (lt_div_iff₀ hm).1 hboundary
    simpa [mul_comm] using hresult

end GaugeAndResolution

end PhonologicalCalculus.ContinuousHG
