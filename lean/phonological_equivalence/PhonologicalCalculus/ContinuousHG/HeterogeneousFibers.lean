                                        
import PhonologicalCalculus.ContinuousHG.HeterogeneousCubeBridge

namespace PhonologicalCalculus.ContinuousHG.HeterogeneousCubeBridge

open Finset HeterogeneousProfileBridge

noncomputable def vectorCurve {N : ℕ} (v : Fin N → ℝ) : Curve
  | 0 => 1
  | k+1 => if hk : k < N then v ⟨k,hk⟩ else 0

theorem vectorCurve_site {N : ℕ} (v : Fin N → ℝ) (i : Fin N) :
    vectorCurve v (i.val+1) = v i := by simp [vectorCurve, i.isLt]

theorem vectorCurve_cube_iff {N : ℕ} (v : Fin N → ℝ) :
    Cube N (vectorCurve v) ↔ ∀ i, 0 ≤ v i ∧ v i ≤ 1 := by
  constructor
  · intro h i
    simpa [vectorCurve, i.isLt] using h.2 (i.val+1) (by omega)
  · intro h
    refine ⟨rfl, ?_⟩
    intro k hk
    cases k with
    | zero => norm_num [vectorCurve]
    | succ k => simpa [vectorCurve, show k < N by omega] using h ⟨k,by omega⟩

theorem vectorCurve_complete {N : ℕ} (x : Curve) (hx : x 0 = 1) :
    ∀ k, k ≤ N → vectorCurve (fun i : Fin N => x (i.val+1)) k = x k := by
  intro k hk
  cases k with
  | zero => exact hx.symm
  | succ k => simp [vectorCurve, show k < N by omega]

theorem envelope_energy_eq_iff {N : ℕ} (h p : ℝ) (m : Fin N → ℝ)
    (hh : 0 < h) (hp : 0 < p) (hm : ∀ i, 0 ≤ m i) (x : Curve) :
    energy h p m (envelope x) = energy h p m x ↔
      (∀ i : Fin N, drop (envelope x) i.val = drop x i.val) ∧
      (∀ i : Fin N, m i = 0 ∨ envelope x (i.val+1) = x (i.val+1)) := by
  have hd : ∀ i : Fin N, (drop (envelope x) i.val)^p ≤ (drop x i.val)^p :=
    fun i => Real.rpow_le_rpow (le_max_right _ _) (envelope_drop_le x i.val) hp.le
  have hm' : ∀ i : Fin N, m i * envelope x (i.val+1) ≤ m i * x (i.val+1) :=
    fun i => mul_le_mul_of_nonneg_left (envelope_le x (i.val+1)) (hm i)
  constructor
  · intro he
    have hds := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin N))) => hd i)
    have hms := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin N))) => hm' i)
    have hed : (∑ i : Fin N, (drop (envelope x) i.val)^p) = ∑ i : Fin N, (drop x i.val)^p := by
      unfold energy at he
      nlinarith
    have hem : (∑ i : Fin N, m i * envelope x (i.val+1)) = ∑ i : Fin N, m i*x (i.val+1) := by
      unfold energy at he
      rw [hed] at he
      linarith
    have hdall := (Finset.sum_eq_sum_iff_of_le (fun i _ => hd i)).mp hed
    have hmall := (Finset.sum_eq_sum_iff_of_le (fun i _ => hm' i)).mp hem
    constructor
    · intro i
      exact (Real.rpow_left_inj (le_max_right _ _) (le_max_right _ _) hp.ne').mp (hdall i (mem_univ i))
    · intro i
      exact mul_eq_mul_left_iff.mp (hmall i (mem_univ i)) |>.symm
  · rintro ⟨hdall,hwall⟩
    unfold energy
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hdall i]
    · apply Finset.sum_congr rfl
      intro i _
      rcases hwall i with hz | he
      · simp [hz]
      · rw [he]

theorem minimizer_envelope_canonical {N : ℕ} (h p : ℝ) (m d : Fin N → ℝ)
    (hh : 0 ≤ h) (hp : 0 ≤ p) (hm : ∀ i, 0 ≤ m i)
    (hd : IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective h 1 p (suffixWeight m)) d)
    (x : Curve) (hx : IsMinimizer h p m x) :
    (∀ k, k ≤ N → envelope x k = profile d k) ∧
      energy h p m (envelope x) = energy h p m x := by
  have he := envelope_cube hx.1
  have hmin := canonical_minimizer h p m d hh hp hm hd
  have ha := hx.2 (profile d) hmin.1
  have hb := hmin.2 (envelope x) he
  have hc := envelope_energy_le h p m hh hp hm x
  have eqe : energy h p m (envelope x) = energy h p m (profile d) := by linarith
  have hds := differences_simplex (envelope x) he (envelope_decreasing x N)
  have eqd : powerReducedObjective h 1 p (suffixWeight m) (differences (envelope x)) =
      powerReducedObjective h 1 p (suffixWeight m) d := by
    rw [energy_decreasing h p m (envelope x) he (envelope_decreasing x N),
      energy_profile h p m d hd.1] at eqe
    linarith
  have heq := (hd.2 _ hds).2 eqd
  constructor
  · intro k hk
    rw [← reconstruct_differences (envelope x) he.1 k hk, heq]
  · linarith

theorem complete_minimizer_fiber {N : ℕ} (h p : ℝ) (m d : Fin N → ℝ)
    (hh : 0 < h) (hp : 0 < p) (hm : ∀ i, 0 ≤ m i)
    (hd : IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective h 1 p (suffixWeight m)) d)
    (x : Curve) (hx : Cube N x) :
    IsMinimizer h p m x ↔
      (∀ k, k ≤ N → envelope x k = profile d k) ∧
      (∀ i : Fin N, drop x i.val = d i) ∧
      (∀ i : Fin N, m i = 0 ∨ x (i.val+1) = profile d (i.val+1)) := by
  have hcan := canonical_minimizer h p m d hh.le hp.le hm hd
  constructor
  · intro hopt
    obtain ⟨heq,he⟩ := minimizer_envelope_canonical h p m d hh.le hp.le hm hd x hopt
    obtain ⟨hdrop,hsite⟩ := (envelope_energy_eq_iff h p m hh hp hm x).mp he
    refine ⟨heq,?_,?_⟩
    · intro i
      rw [← hdrop i]
      unfold drop
      rw [heq i.val (by omega), heq (i.val+1) (by omega), profile_step, max_eq_left (hd.1.1 i)]
    · intro i
      rcases hsite i with hz | he
      · exact Or.inl hz
      · exact Or.inr (he.symm.trans (heq _ (by omega)))
  · rintro ⟨heq,hdrop,hsite⟩
    have he : energy h p m x = energy h p m (profile d) := by
      unfold energy
      congr 1
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hdrop i]
        unfold drop
        rw [profile_step, max_eq_left (hd.1.1 i)]
      · apply Finset.sum_congr rfl
        intro i _
        rcases hsite i with hz | he
        · simp [hz]
        · rw [he]
    refine ⟨hx, ?_⟩
    intro y hy
    rw [he]
    exact hcan.2 y hy

theorem positive_sites_unique {N : ℕ} (h p : ℝ) (m d : Fin N → ℝ)
    (hh : 0 < h) (hp : 0 < p) (hm : ∀ i, 0 < m i)
    (hd : IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective h 1 p (suffixWeight m)) d)
    (x : Curve) (hx : IsMinimizer h p m x) :
    ∀ k, k ≤ N → x k = profile d k := by
  have hf := (complete_minimizer_fiber h p m d hh hp (fun i => (hm i).le) hd x hx.1).mp hx
  intro k hk
  cases k with
  | zero => simpa [profile_zero] using hx.1.1
  | succ k =>
    have hi : k < N := by omega
    exact (hf.2.2 ⟨k,hi⟩).resolve_left (ne_of_gt (hm ⟨k,hi⟩))

theorem cube_kkt_and_complete_fiber {N : ℕ} (h p : ℝ) (m : Fin N → ℝ)
    (hh : 0 < h) (hp : 1 < p) (hm : ∀ i, 0 ≤ m i) :
    ∃ eta : ℝ, 0 ≤ eta ∧
      let d := powerKKTDecrease h 1 p eta (suffixWeight m)
      SolidSimplex d ∧ eta * (1-∑ i, d i) = 0 ∧
      IsMinimizer h p m (profile d) ∧
      (∀ x, Cube N x → (IsMinimizer h p m x ↔
        (∀ k, k ≤ N → envelope x k = profile d k) ∧
        (∀ i : Fin N, drop x i.val = d i) ∧
        (∀ i : Fin N, m i = 0 ∨ x (i.val+1) = profile d (i.val+1)))) := by
  obtain ⟨eta,he,hs,hc,hu,ho⟩ := exists_canonical_optimizer h p m hh hp hm
  exact ⟨eta,he,hs,hc,ho,fun x hx => complete_minimizer_fiber h p m _ hh (by linarith) hm hu x hx⟩

theorem positive_sites_finite_unique {N : ℕ} (h p : ℝ) (m : Fin N → ℝ)
    (hh : 0 < h) (hp : 1 < p) (hm : ∀ i, 0 < m i) :
    ∃! v : Fin N → ℝ, IsMinimizer h p m (vectorCurve v) := by
  obtain ⟨eta,he,hs,hc,hu,ho⟩ := exists_canonical_optimizer h p m hh hp (fun i => (hm i).le)
  let d := powerKKTDecrease h 1 p eta (suffixWeight m)
  let v : Fin N → ℝ := fun i => profile d (i.val+1)
  have hvc : Cube N (vectorCurve v) := (vectorCurve_cube_iff v).mpr (fun i => profile_bounds d hs _)
  have hev : energy h p m (vectorCurve v) = energy h p m (profile d) :=
    energy_congr h p m _ _ (vectorCurve_complete (profile d) (profile_zero d))
  refine ⟨v,⟨hvc,fun y hy => hev ▸ ho.2 y hy⟩,?_⟩
  intro w hw
  funext i
  have hhx := positive_sites_unique h p m d hh (by linarith) hm hu (vectorCurve w) hw (i.val+1) (by omega)
  simpa only [vectorCurve_site] using hhx

end PhonologicalCalculus.ContinuousHG.HeterogeneousCubeBridge
