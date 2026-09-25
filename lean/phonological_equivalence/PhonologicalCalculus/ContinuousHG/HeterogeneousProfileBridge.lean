                                                           
import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer

namespace PhonologicalCalculus.ContinuousHG.HeterogeneousProfileBridge

open Finset

noncomputable def profile {N : ℕ} (d : Fin N → ℝ) (k : ℕ) : ℝ :=
  1 - ∑ i : Fin N, if i.val < k then d i else 0

noncomputable def suffixWeight {N : ℕ} (m : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin N, if i ≤ j then m j else 0

theorem profile_zero {N : ℕ} (d : Fin N → ℝ) : profile d 0 = 1 := by
  simp [profile]

theorem profile_step {N : ℕ} (d : Fin N → ℝ) (i : Fin N) :
    profile d i.val - profile d (i.val+1) = d i := by
  have he : (∑ j : Fin N, if j.val < i.val+1 then d j else 0) =
      (∑ j : Fin N, if j.val < i.val then d j else 0) + d i := by
    have ht : ∀ j : Fin N, (if j.val < i.val+1 then d j else 0) =
        (if j.val < i.val then d j else 0) + (if j=i then d i else 0) := by
      intro j
      by_cases hji : j=i
      · subst j; simp
      · have hn : j.val ≠ i.val := fun h => hji (Fin.ext h)
        split_ifs <;> simp_all <;> omega
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  unfold profile
  linarith

theorem profile_bounds {N : ℕ} (d : Fin N → ℝ) (hd : SolidSimplex d) (k : ℕ) :
    0 ≤ profile d k ∧ profile d k ≤ 1 := by
  have hn : 0 ≤ ∑ i : Fin N, if i.val < k then d i else 0 := by
    apply Finset.sum_nonneg; intro i _; split_ifs; exact hd.1 i; rfl
  have hu : (∑ i : Fin N, if i.val < k then d i else 0) ≤ ∑ i, d i := by
    apply Finset.sum_le_sum; intro i _; split_ifs; rfl; exact hd.1 i
  unfold profile
  constructor <;> linarith [hd.2]

theorem profile_last {N : ℕ} (d : Fin N → ℝ) :
    profile d N = 1 - ∑ i, d i := by
  simp [profile]

theorem weighted_profile_identity {N : ℕ} (m d : Fin N → ℝ) :
    (∑ j : Fin N, m j * profile d (j.val+1)) =
      (∑ j, m j) - ∑ i, suffixWeight m i * d i := by
  simp only [profile, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [suffixWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≤ j
  · have hlt : i.val < j.val+1 := by omega
    simp [hij,hlt]
  · have hlt : ¬i.val < j.val+1 := by omega
    simp [hij,hlt]

theorem original_reduced_identity {N : ℕ} (h p : ℝ) (m d : Fin N → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    h * (∑ i : Fin N, (max (profile d i.val-profile d (i.val+1)) 0)^p) +
      (∑ j : Fin N, m j * profile d (j.val+1)) =
    (∑ j, m j) + powerReducedObjective h 1 p (suffixWeight m) d := by
  simp_rw [profile_step, max_eq_left (hd _)]
  rw [weighted_profile_identity]
  simp only [powerReducedObjective, one_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end PhonologicalCalculus.ContinuousHG.HeterogeneousProfileBridge
