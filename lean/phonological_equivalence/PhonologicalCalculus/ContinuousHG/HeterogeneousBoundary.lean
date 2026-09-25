                                                
import PhonologicalCalculus.ContinuousHG.Heterogeneous

namespace PhonologicalCalculus.ContinuousHG.HeterogeneousBoundary

open Heterogeneous Finset

theorem reduced_optimizer_exists {N : ℕ} (h p : ℝ) (hh : 0 < h)
    (hp : 1 < p) (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i) :
    ∃ eta : ℝ, 0 ≤ eta ∧
      (eta = 0 ∨ powerKKTMass h 1 p eta (cumulative m) = 1) ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective h 1 p (cumulative m))
        (powerKKTDecrease h 1 p eta (cumulative m)) := by
  by_cases hz : powerKKTMass h 1 p 0 (cumulative m) ≤ 1
  · exact ⟨0, le_rfl, Or.inl rfl,
      powerKKTDecrease_zero_unique_minimizer (cumulative m) hh hp hz⟩
  · have hup : 0 ≤ ∑ i, m i := Finset.sum_nonneg fun i _ => hm i
    have hbound : ∀ i, 1 * cumulative m i ≤ ∑ j, m j := by
      intro i
      simp only [one_mul, cumulative]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hm j)
    obtain ⟨eta, he, _, hmass⟩ := exists_powerKKT_multiplier
      (cumulative m) hh hp hup hbound (le_of_not_ge hz)
    exact ⟨eta, he, Or.inr hmass,
      powerKKTDecrease_unique_minimizer (cumulative m) hh hp he hmass⟩

noncomputable def twoSiteEnergy (c x y : ℝ) : ℝ :=
  (max (1-x) 0)^2 + (max (x-y) 0)^2 + c*x

theorem two_site_original_correspondence (c x y : ℝ) :
    heteroHarmony 2 1 [c,0] [x,y] = twoSiteEnergy c x y := by
  simp [heteroHarmony, directionalDrops, directionalDropsFrom, directionalDrop,
    realPowerPenalty, twoSiteEnergy]

theorem two_site_complete_square (c x y : ℝ) (hx : x ≤ 1) :
    twoSiteEnergy c x y = (x-(1-c/2))^2 + c-c^2/4 + (max (x-y) 0)^2 := by
  unfold twoSiteEnergy
  rw [max_eq_left (sub_nonneg.mpr hx)]
  ring

theorem two_site_lower_bound (c x y : ℝ) (hx : x ≤ 1) :
    c-c^2/4 ≤ twoSiteEnergy c x y := by
  rw [two_site_complete_square c x y hx]
  nlinarith [sq_nonneg (x-(1-c/2)), sq_nonneg (max (x-y) 0)]

theorem two_site_complete_argmin (c x y : ℝ) (hx : x ≤ 1) :
    twoSiteEnergy c x y = c-c^2/4 ↔ x=1-c/2 ∧ x≤y := by
  rw [two_site_complete_square c x y hx]
  constructor
  · intro h
    have he : x=1-c/2 := by
      nlinarith [sq_nonneg (x-(1-c/2)),sq_nonneg (max (x-y) 0)]
    have hz : max (x-y) 0 = 0 := by
      nlinarith [sq_nonneg (x-(1-c/2)),le_max_right (x-y) 0]
    exact ⟨he,by linarith [le_max_left (x-y) 0]⟩
  · rintro ⟨rfl,hxy⟩
    rw [max_eq_right (sub_nonpos.mpr hxy)]
    ring

theorem saturated_original_argmin (x y : ℝ) (hx : x ≤ 1) (hy : 0 ≤ y) :
    heteroHarmony 2 1 [2,0] [x,y] = 1 ↔ x=0 := by
  rw [two_site_original_correspondence]
  have hh := two_site_complete_argmin 2 x y hx
  norm_num at hh
  constructor
  · exact fun h => (hh.mp h).1
  · intro h
    exact hh.mpr ⟨h,h ▸ hy⟩

theorem saturated_distinct_minimizers :
    heteroHarmony 2 1 [2,0] [0,0] = 1 ∧
    heteroHarmony 2 1 [2,0] [0,1] = 1 ∧
    ([0,0] : List ℝ) ≠ [0,1] ∧
    ∀ x y : ℝ, x ≤ 1 → 1 ≤ heteroHarmony 2 1 [2,0] [x,y] := by
  refine ⟨(saturated_original_argmin 0 0 (by norm_num) (by norm_num)).mpr rfl,
    (saturated_original_argmin 0 1 (by norm_num) (by norm_num)).mpr rfl,
    by norm_num, ?_⟩
  intro x y hx
  rw [two_site_original_correspondence]
  have hb := two_site_lower_bound 2 x y hx
  norm_num at hb
  exact hb

noncomputable def zeroEnergyFrom (previous : ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => (max (previous-x) 0)^2 + zeroEnergyFrom x xs

theorem zero_energy_nonnegative (a : ℝ) (xs : List ℝ) : 0 ≤ zeroEnergyFrom a xs := by
  induction xs generalizing a with
  | nil => simp [zeroEnergyFrom]
  | cons x xs ih =>
    simpa only [zeroEnergyFrom] using add_nonneg (sq_nonneg (max (a-x) 0)) (ih x)

theorem all_zero_sites_unique (xs : List ℝ) (hb : ∀ x ∈ xs, x ≤ 1) :
    zeroEnergyFrom 1 xs = 0 ↔ ∀ x ∈ xs, x=1 := by
  induction xs with
  | nil => simp [zeroEnergyFrom]
  | cons x xs ih =>
    have hx : x ≤ 1 := hb x (by simp)
    have hs : ∀ z ∈ xs, z ≤ 1 := fun z hz => hb z (by simp [hz])
    rw [zeroEnergyFrom]
    constructor
    · intro h
      have hnon := zero_energy_nonnegative x xs
      have he : x=1 := by
        rw [max_eq_left (sub_nonneg.mpr hx)] at h
        nlinarith [sq_nonneg (1-x)]
      subst x
      simp only [sub_self, max_self, zero_pow (by decide : 2 ≠ 0), zero_add] at h
      have ht := (ih hs).mp h
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rfl
      · exact ht z hz
    · intro hall
      have he : x=1 := hall x (by simp)
      subst x
      simp only [sub_self,max_self,zero_pow (by decide : 2 ≠ 0),zero_add]
      exact (ih hs).mpr (fun z hz => hall z (by simp [hz]))

theorem zero_energy_original_correspondence (xs : List ℝ) :
    heteroHarmony 2 1 (List.replicate xs.length 0) xs = zeroEnergyFrom 1 xs := by
  have hgeneral : ∀ (a : ℝ) (ys : List ℝ),
      ((directionalDropsFrom a ys).map (realPowerPenalty 2)).sum = zeroEnergyFrom a ys := by
    intro a ys
    induction ys generalizing a with
    | nil => simp [directionalDropsFrom,zeroEnergyFrom]
    | cons y ys ih => simp [directionalDropsFrom,zeroEnergyFrom,directionalDrop,realPowerPenalty,ih]
  have hsite : ∀ ys : List ℝ,
      (List.zipWith (· * ·) (List.replicate ys.length (0:ℝ)) ys).sum = 0 := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.sum_cons, zero_mul, zero_add]
      exact ih
  simp [heteroHarmony,directionalDrops,hsite,hgeneral]

theorem negative_single_site_unique (x : ℝ) (hx : x ≤ 1) :
    -1 ≤ heteroHarmony 2 1 [-1] [x] ∧
      (heteroHarmony 2 1 [-1] [x] = -1 ↔ x=1) := by
  have he : heteroHarmony 2 1 [-1] [x] = (1-x)^2-x := by
    simp [heteroHarmony,directionalDrops,directionalDropsFrom,directionalDrop,
      realPowerPenalty,max_eq_left (sub_nonneg.mpr hx)]
    ring
  rw [he]
  constructor
  · nlinarith [sq_nonneg (1-x)]
  · constructor
    · intro h
      nlinarith [sq_nonneg (1-x)]
    · intro h
      rw [h]
      norm_num

end PhonologicalCalculus.ContinuousHG.HeterogeneousBoundary
