                                                        
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace PhonologicalCalculus
namespace MaxEnt
namespace Productive

open Real

theorem choose_le_pow (n k : ℕ) : (n + k).choose n ≤ (k + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.add_one_mul_choose_eq (n + k) n
    rw [show n + 1 + k = n + k + 1 by omega]
    have hb : (n + k + 1) * (n + k).choose n ≤ (n + k + 1) * (k + 1) ^ n := Nat.mul_le_mul_left _ ih
    have hc : (n + k + 1) * (k + 1) ^ n ≤ ((n + 1) * (k + 1)) * (k + 1) ^ n := by
      apply Nat.mul_le_mul_right
      nlinarith
    have hd : (n + 1) * (k + 1) * (k + 1) ^ n = (n + 1) * (k + 1) ^ (n + 1) := by ring
    have he : (n + 1) * ((n + k + 1).choose (n + 1)) ≤ (n + 1) * (k + 1) ^ (n + 1) := by
      calc (n + 1) * ((n + k + 1).choose (n + 1)) = (n + k + 1).choose (n + 1) * (n + 1) := by ring
        _ = (n + k + 1) * (n + k).choose n := h.symm
        _ ≤ (n + 1) * (k + 1) ^ (n + 1) := by omega
    exact Nat.le_of_mul_le_mul_left he (Nat.succ_pos n)

theorem ratio_lt_one_iff (m δ T : ℝ) (hm : 1 < m) (hT : 0 < T) :
    m * exp (-(δ / T)) < 1 ↔ T < δ / log m := by
  have hlog : 0 < log m := Real.log_pos hm
  have hm0 : 0 < m := by linarith
  constructor
  · intro h
    have h1 : exp (-(δ / T)) < 1 / m := by
      rw [lt_div_iff₀ hm0]; linarith [mul_comm m (exp (-(δ / T)))]
    have h2 : -(δ / T) < log (1 / m) := by
      rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]; exact h1
    rw [Real.log_div (by norm_num) hm0.ne', Real.log_one, zero_sub] at h2
    have h3 : log m < δ / T := by linarith
    rw [lt_div_iff₀ hT] at h3
    rw [lt_div_iff₀ hlog]
    linarith
  · intro h
    rw [lt_div_iff₀ hlog] at h
    have h3 : log m < δ / T := by rw [lt_div_iff₀ hT]; linarith
    have h2 : -(δ / T) < log (1 / m) := by
      rw [Real.log_div (by norm_num) hm0.ne', Real.log_one, zero_sub]; linarith
    have h1 : exp (-(δ / T)) < 1 / m := by
      rw [← Real.exp_log (show (0:ℝ) < 1 / m by positivity)]
      exact Real.exp_lt_exp.mpr h2
    rw [lt_div_iff₀ hm0] at h1
    linarith [mul_comm (exp (-(δ / T))) m]

theorem summable_shifted_pow_mul_geometric (n : ℕ) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ n * r ^ k) := by
  have h : Summable (fun k : ℕ => (k : ℝ) ^ n * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one n (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr)
  have h2 := (summable_nat_add_iff 1).mpr h
  have h3 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ n * r ^ (k + 1)) * r⁻¹) := h2.mul_right r⁻¹
  refine h3.congr ?_
  intro k
  push_cast
  field_simp
  try ring

theorem partition_summable (A : ℝ) (n : ℕ) (m δ T : ℝ) (hm : 1 < m) (hT : 0 < T)
    (hTc : T < δ / log m) (N : ℕ → ℝ) (hN : ∀ k, 0 ≤ N k)
    (hNb : ∀ k, N k ≤ A * ((k : ℝ) + 1) ^ n * m ^ k) :
    Summable (fun k : ℕ => N k * exp (-(δ * k) / T)) := by
  have hr := (ratio_lt_one_iff m δ T hm hT).mpr hTc
  have hm0 : 0 < m := by linarith
  have hr0 : 0 < m * exp (-(δ / T)) := by positivity
  have hs := summable_shifted_pow_mul_geometric n (m * exp (-(δ / T))) hr0 hr
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hs.mul_left A)
  · have := hN k
    positivity
  · have h1 : exp (-(δ * k) / T) = (exp (-(δ / T))) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      try ring
    rw [h1, mul_pow]
    have h2 := hNb k
    have h3 : 0 ≤ exp (-(δ / T)) ^ k := by positivity
    calc N k * exp (-(δ / T)) ^ k ≤ A * ((k : ℝ) + 1) ^ n * m ^ k * exp (-(δ / T)) ^ k :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = A * (((k : ℝ) + 1) ^ n * (m ^ k * exp (-(δ / T)) ^ k)) := by ring

theorem partition_diverges (m δ T : ℝ) (hm : 1 < m) (hT : 0 < T) (hTc : δ / log m ≤ T)
    (N : ℕ → ℝ) (hNb : ∀ k, m ^ k ≤ N k) :
    ¬ Summable (fun k : ℕ => N k * exp (-(δ * k) / T)) := by
  intro hs
  have hm0 : 0 < m := by linarith
  have hr : 1 ≤ m * exp (-(δ / T)) := by
    by_contra hlt
    have := (ratio_lt_one_iff m δ T hm hT).mp (lt_of_not_ge hlt)
    linarith
  have hgeom : Summable (fun k : ℕ => (m * exp (-(δ / T))) ^ k) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
    have h1 : exp (-(δ * k) / T) = (exp (-(δ / T))) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      try ring
    rw [h1, mul_pow]
    exact mul_le_mul_of_nonneg_right (hNb k) (by positivity)
  have := summable_geometric_iff_norm_lt_one.mp hgeom
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith

end Productive
end MaxEnt
end PhonologicalCalculus
