                                                
import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PhonologicalCalculus.ContinuousHG
namespace Heterogeneous

open Finset

noncomputable def heteroHarmony (p h : ℝ) (m profile : List ℝ) : ℝ :=
  h * ((directionalDrops profile).map (realPowerPenalty p)).sum + (List.zipWith (· * ·) m profile).sum

theorem zipWith_sum_mono (m : List ℝ) (hm : ∀ x ∈ m, 0 ≤ x) :
    ∀ {a b : List ℝ}, List.Forall₂ (· ≤ ·) a b →
      (List.zipWith (· * ·) m a).sum ≤ (List.zipWith (· * ·) m b).sum := by
  intro a b hab
  induction hab generalizing m with
  | nil => simp
  | cons hxy _ ih =>
    cases m with
    | nil => simp
    | cons w ws =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have hw : 0 ≤ w := hm w (List.mem_cons_self)
      have hws : ∀ x ∈ ws, 0 ≤ x := fun x hx => hm x (List.mem_cons_of_mem _ hx)
      exact add_le_add (mul_le_mul_of_nonneg_left hxy hw) (ih ws hws)

                            
theorem heteroHarmony_runningMinimum_le (p h : ℝ) (hp : 1 < p) (hh : 0 ≤ h) (m profile : List ℝ)
    (hm : ∀ x ∈ m, 0 ≤ x) :
    heteroHarmony p h m (runningMinimum profile) ≤ heteroHarmony p h m profile := by
  unfold heteroHarmony
  have h1 := runningMinimum_directional_penalty_le (realPowerPenalty p)
    (fun a b ha hab => realPowerPenalty_monotone_on_nonnegative hp ha hab) profile
  have h2 := zipWith_sum_mono m hm (runningMinimumFrom_coordinatewise_le 1 profile)
  have h3 : h * ((directionalDrops (runningMinimum profile)).map (realPowerPenalty p)).sum
      ≤ h * ((directionalDrops profile).map (realPowerPenalty p)).sum := mul_le_mul_of_nonneg_left h1 hh
  unfold runningMinimum at h3 ⊢
  linarith

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
                            
theorem powerKKTDecrease_mono_weight {h m p eta : ℝ} (M : ι → ℝ) (hh : 0 < h) (hp : 1 < p) (hm : 0 ≤ m)
    {i j : ι} (hij : M i ≤ M j) :
    powerKKTDecrease h m p eta M i ≤ powerKKTDecrease h m p eta M j := by
  unfold powerKKTDecrease
  have hden : 0 < p * h := mul_pos (lt_trans zero_lt_one hp) hh
  have hq : 0 ≤ powerShiftExponent p := (powerShiftExponent_positive hp).le
  apply Real.rpow_le_rpow
  · exact div_nonneg (le_max_right _ _) hden.le
  · apply div_le_div_of_nonneg_right _ hden.le
    apply max_le_max_right
    linarith [mul_le_mul_of_nonneg_left hij hm]
  · exact hq

noncomputable def cumulative {N : ℕ} (m : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ univ.filter (fun j => i ≤ j), m j

theorem cumulative_antitone {N : ℕ} (m : Fin N → ℝ) (hm : ∀ j, 0 ≤ m j) : Antitone (cumulative m) := by
  intro i i' hii'
  unfold cumulative
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact le_trans hii' hj
  · intro j _ _
    exact hm j

                            
theorem hetero_unique_minimizer {N : ℕ} (h p eta : ℝ) (hh : 0 < h) (hp : 1 < p) (m : Fin N → ℝ)
    (heta : 0 ≤ eta) (hmass : powerKKTMass h 1 p eta (cumulative m) = 1) :
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop) (powerReducedObjective h 1 p (cumulative m))
      (powerKKTDecrease h 1 p eta (cumulative m)) :=
  powerKKTDecrease_unique_minimizer (cumulative m) hh hp heta hmass

                            
theorem hetero_decreases_antitone {N : ℕ} (h p eta : ℝ) (hh : 0 < h) (hp : 1 < p) (m : Fin N → ℝ)
    (hm : ∀ j, 0 ≤ m j) : Antitone (powerKKTDecrease h 1 p eta (cumulative m)) := by
  intro i j hij
  exact powerKKTDecrease_mono_weight (cumulative m) hh hp zero_le_one (cumulative_antitone m hm hij)

theorem profile_antitone_zero_tail {N : ℕ} (x : Fin N → ℝ) (hx : Antitone x) (hnn : ∀ i, 0 ≤ x i)
    {i j : Fin N} (hij : i ≤ j) (hzero : x i = 0) : x j = 0 :=
  le_antisymm (hzero ▸ hx hij) (hnn j)

noncomputable def extended {N R : ℕ} (M : Fin N → ℝ) (C : ℝ) (Mnew : Fin R → ℝ) : Fin (N + R) → ℝ :=
  fun k => Fin.addCases (fun i => M i + C) (fun j => Mnew j) k

                            
theorem hetero_extension_stable {N R : ℕ} (h p eta : ℝ) (hh : 0 < h) (hp : 1 < p) (heta : 0 ≤ eta)
    (M : Fin N → ℝ) (hmass : powerKKTMass h 1 p eta M = 1) (C : ℝ) (hC : 0 ≤ C)
    (Mnew : Fin R → ℝ) (hnew : ∀ j, Mnew j ≤ C) :
    (∀ i : Fin N, powerKKTDecrease h 1 p (eta + C) (extended M C Mnew) (Fin.castAdd R i)
        = powerKKTDecrease h 1 p eta M i) ∧
    (∀ j : Fin R, powerKKTDecrease h 1 p (eta + C) (extended M C Mnew) (Fin.natAdd N j) = 0) ∧
    IsUniqueMinimizerOn (SolidSimplex : (Fin (N + R) → ℝ) → Prop)
      (powerReducedObjective h 1 p (extended M C Mnew))
      (powerKKTDecrease h 1 p (eta + C) (extended M C Mnew)) := by
  have hold : ∀ i : Fin N, powerKKTDecrease h 1 p (eta + C) (extended M C Mnew) (Fin.castAdd R i)
      = powerKKTDecrease h 1 p eta M i := by
    intro i
    unfold powerKKTDecrease extended
    simp only [Fin.addCases_left, one_mul]
    congr 2
    ring
  have hnewz : ∀ j : Fin R, powerKKTDecrease h 1 p (eta + C) (extended M C Mnew) (Fin.natAdd N j) = 0 := by
    intro j
    unfold powerKKTDecrease extended
    simp only [Fin.addCases_right, one_mul]
    have : max (Mnew j - (eta + C)) 0 = 0 := by
      apply max_eq_right
      linarith [hnew j]
    rw [this, zero_div, Real.zero_rpow (powerShiftExponent_positive hp).ne']
  refine ⟨hold, hnewz, ?_⟩
  apply powerKKTDecrease_unique_minimizer _ hh hp (by linarith)
  unfold powerKKTMass
  rw [Fin.sum_univ_add]
  simp only [hold, hnewz, Finset.sum_const_zero, add_zero]
  exact hmass

omit [Fintype ι] in
                            
theorem hetero_unsaturated_shift (h p : ℝ) (hh : 0 < h) (hp : 1 < p) (M : ι → ℝ) (C : ℝ) (hC : 0 < C)
    (i : ι) (hi : 0 ≤ M i) :
    powerKKTDecrease h 1 p 0 M i < powerKKTDecrease h 1 p 0 (fun k => M k + C) i := by
  unfold powerKKTDecrease
  have hden : 0 < p * h := mul_pos (lt_trans zero_lt_one hp) hh
  apply Real.rpow_lt_rpow
  · exact div_nonneg (le_max_right _ _) hden.le
  · apply div_lt_div_of_pos_right _ hden
    simp only [one_mul, sub_zero]
    rw [max_eq_left hi, max_eq_left (by linarith)]
    linarith
  · exact powerShiftExponent_positive hp

def obstructionSites : List ℤ := [1, 1, -4, 1, 1, 1]

def dropsFrom (previous : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: xs => (max (previous - x) 0) :: dropsFrom x xs

def scaledEnergy (m x : List ℤ) : ℤ :=
  5 * ((dropsFrom 8 x).map (fun d => d * d)).sum + 8 * (List.zipWith (· * ·) m x).sum

def isMonotone : ℤ → List ℤ → Bool
  | _, [] => true
  | prev, x :: xs => decide (x ≤ prev) && isMonotone x xs

def monoGrid : ℤ → ℕ → List (List ℤ)
  | _, 0 => [[]]
  | prev, n + 1 => (List.range 9).flatMap (fun k => if (k : ℤ) ≤ prev then (monoGrid (k : ℤ) n).map (fun v => (k : ℤ) :: v) else [])

def monotoneMinimum : ℤ :=
  (monoGrid 8 6).foldl (fun acc v => min acc (scaledEnergy obstructionSites v)) 1000

theorem monoGrid_length : (monoGrid 8 6).length = 3003 := by
  decide +kernel

                      
theorem obstruction_witness :
    scaledEnergy obstructionSites [6, 5, 8, 6, 4, 3] = 6 ∧
    scaledEnergy obstructionSites [7, 7, 7, 5, 3, 2] = 18 ∧
    isMonotone 8 [6, 5, 8, 6, 4, 3] = false ∧
    isMonotone 8 [7, 7, 7, 5, 3, 2] = true ∧
    [7, 7, 7, 5, 3, 2] ∈ monoGrid 8 6 ∧
    monotoneMinimum = 18 := by
  decide +kernel

end Heterogeneous
end PhonologicalCalculus.ContinuousHG
