                                                                       
import PhonologicalCalculus.ContinuousHG.HeterogeneousBoundary
import PhonologicalCalculus.ContinuousHG.HeterogeneousProfileBridge

namespace PhonologicalCalculus.ContinuousHG.HeterogeneousCubeBridge

open Finset HeterogeneousProfileBridge

abbrev Curve := ℕ → ℝ

def Cube (N : ℕ) (x : Curve) : Prop :=
  x 0 = 1 ∧ ∀ k, k ≤ N → 0 ≤ x k ∧ x k ≤ 1

def Decreasing (N : ℕ) (x : Curve) : Prop :=
  ∀ k, k < N → x (k+1) ≤ x k

noncomputable def envelope (x : Curve) : Curve
  | 0 => x 0
  | k+1 => min (envelope x k) (x (k+1))

noncomputable def drop (x : Curve) (k : ℕ) : ℝ := max (x k-x (k+1)) 0

noncomputable def energy {N : ℕ} (h p : ℝ) (m : Fin N → ℝ) (x : Curve) : ℝ :=
  h * ∑ i : Fin N, (drop x i.val)^p + ∑ i : Fin N, m i * x (i.val+1)

def IsMinimizer {N : ℕ} (h p : ℝ) (m : Fin N → ℝ) (x : Curve) : Prop :=
  Cube N x ∧ ∀ y, Cube N y → energy h p m x ≤ energy h p m y

noncomputable def differences {N : ℕ} (x : Curve) : Fin N → ℝ :=
  fun i => x i.val - x (i.val+1)

theorem envelope_le (x : Curve) (k : ℕ) : envelope x k ≤ x k := by
  cases k with
  | zero => rfl
  | succ k => exact min_le_right _ _

theorem envelope_decreasing (x : Curve) (N : ℕ) : Decreasing N (envelope x) := by
  intro k _
  exact min_le_left _ _

theorem envelope_cube {N : ℕ} {x : Curve} (hx : Cube N x) : Cube N (envelope x) := by
  refine ⟨hx.1, ?_⟩
  intro k hk
  refine ⟨?_, le_trans (envelope_le x k) (hx.2 k hk).2⟩
  induction k with
  | zero => exact (hx.2 0 (by omega)).1
  | succ k ih =>
    exact le_min (ih (by omega)) (hx.2 (k+1) hk).1

theorem envelope_drop_le (x : Curve) (k : ℕ) : drop (envelope x) k ≤ drop x k := by
  exact directionalDrop_running_min_le (envelope_le x k)

theorem envelope_energy_le {N : ℕ} (h p : ℝ) (m : Fin N → ℝ)
    (hh : 0 ≤ h) (hp : 0 ≤ p) (hm : ∀ i, 0 ≤ m i) (x : Curve) :
    energy h p m (envelope x) ≤ energy h p m x := by
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hh
    apply Finset.sum_le_sum
    intro i _
    exact Real.rpow_le_rpow (le_max_right _ _) (envelope_drop_le x i.val) hp
  · apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (envelope_le x (i.val+1)) (hm i)

theorem reconstruct_differences {N : ℕ} (x : Curve) (hx : x 0 = 1)
    (k : ℕ) (hk : k ≤ N) : profile (differences (N:=N) x) k = x k := by
  induction k with
  | zero => simpa [profile_zero] using hx.symm
  | succ k ih =>
    have hi : k < N := by omega
    have hs := profile_step (differences (N:=N) x) ⟨k,hi⟩
    simp only [differences] at hs
    have he := ih (by omega)
    linarith

theorem differences_simplex {N : ℕ} (x : Curve) (hx : Cube N x)
    (hm : Decreasing N x) : SolidSimplex (differences (N:=N) x) := by
  refine ⟨fun i => sub_nonneg.mpr (hm i.val i.isLt), ?_⟩
  have hr := reconstruct_differences x hx.1 N (le_refl N)
  rw [profile_last] at hr
  linarith [(hx.2 N (le_refl N)).1]

theorem profile_cube {N : ℕ} (d : Fin N → ℝ) (hd : SolidSimplex d) :
    Cube N (profile d) := by
  exact ⟨profile_zero d, fun k _ => profile_bounds d hd k⟩

theorem profile_decreasing {N : ℕ} (d : Fin N → ℝ) (hd : SolidSimplex d) :
    Decreasing N (profile d) := by
  intro k hk
  have hs := profile_step d ⟨k,hk⟩
  dsimp at hs
  linarith [hd.1 ⟨k,hk⟩]

theorem differences_profile {N : ℕ} (d : Fin N → ℝ) :
    differences (profile d) = d := by
  funext i
  exact profile_step d i

theorem energy_congr {N : ℕ} (h p : ℝ) (m : Fin N → ℝ) (x y : Curve)
    (he : ∀ k, k ≤ N → x k = y k) : energy h p m x = energy h p m y := by
  unfold energy
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [drop, he i.val (by omega), he (i.val+1) (by omega)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [he (i.val+1) (by omega)]

theorem energy_profile {N : ℕ} (h p : ℝ) (m d : Fin N → ℝ) (hd : SolidSimplex d) :
    energy h p m (profile d) = (∑ i, m i) + powerReducedObjective h 1 p (suffixWeight m) d :=
  original_reduced_identity h p m d hd.1

theorem energy_decreasing {N : ℕ} (h p : ℝ) (m : Fin N → ℝ) (x : Curve)
    (hx : Cube N x) (hm : Decreasing N x) :
    energy h p m x = (∑ i, m i) + powerReducedObjective h 1 p (suffixWeight m) (differences x) := by
  rw [← energy_profile h p m (differences x) (differences_simplex x hx hm)]
  exact energy_congr h p m x _ (fun k hk => (reconstruct_differences x hx.1 k hk).symm)

theorem suffix_eq_cumulative {N : ℕ} (m : Fin N → ℝ) : suffixWeight m = Heterogeneous.cumulative m := by
  funext i
  simp [suffixWeight, Heterogeneous.cumulative, Finset.sum_filter]

theorem canonical_minimizer {N : ℕ} (h p : ℝ) (m d : Fin N → ℝ)
    (hh : 0 ≤ h) (hp : 0 ≤ p) (hm : ∀ i, 0 ≤ m i)
    (hd : IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective h 1 p (suffixWeight m)) d) :
    IsMinimizer h p m (profile d) := by
  refine ⟨profile_cube d hd.1, ?_⟩
  intro x hx
  have he := envelope_cube hx
  have hs := differences_simplex (envelope x) he (envelope_decreasing x N)
  have hmin := (hd.2 (differences (envelope x)) hs).1
  have hcomp : energy h p m (profile d) ≤ energy h p m (envelope x) := by
    rw [energy_profile h p m d hd.1, energy_decreasing h p m (envelope x) he (envelope_decreasing x N)]
    linarith
  exact le_trans hcomp (envelope_energy_le h p m hh hp hm x)

theorem exists_canonical_optimizer {N : ℕ} (h p : ℝ) (m : Fin N → ℝ)
    (hh : 0 < h) (hp : 1 < p) (hm : ∀ i, 0 ≤ m i) :
    ∃ eta : ℝ, 0 ≤ eta ∧
      let d := powerKKTDecrease h 1 p eta (suffixWeight m)
      SolidSimplex d ∧ eta * (1-∑ i, d i) = 0 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective h 1 p (suffixWeight m)) d ∧
      IsMinimizer h p m (profile d) := by
  obtain ⟨eta,heta,hcomp,hmin⟩ := HeterogeneousBoundary.reduced_optimizer_exists h p hh hp m hm
  rw [← suffix_eq_cumulative] at hcomp hmin
  refine ⟨eta,heta,hmin.1,?_,hmin,canonical_minimizer h p m _ hh.le (by linarith) hm hmin⟩
  rcases hcomp with hz | hs
  · simp [hz]
  · unfold powerKKTMass at hs
    rw [hs]
    ring

end PhonologicalCalculus.ContinuousHG.HeterogeneousCubeBridge
