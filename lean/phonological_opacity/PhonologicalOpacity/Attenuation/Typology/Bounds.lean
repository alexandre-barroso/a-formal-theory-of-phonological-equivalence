import PhonologicalOpacity.Attenuation.MutualCounterfeeding
namespace InteractionTypology
theorem quadratic_half_iff (l : ℝ) (hl : 0≤l) :
    0<1-2*l^2 ↔ l<1/Real.sqrt 2 := by
  have hr : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (1:ℝ)/Real.sqrt 2=Real.sqrt 2/2 := by
    apply (div_eq_div_iff (ne_of_gt hr) (by norm_num : (2:ℝ)≠0)).mpr
    nlinarith
  rw [hi]
  constructor
  · intro h
    by_contra hn
    have hge : Real.sqrt 2/2≤l := le_of_not_gt hn
    nlinarith [mul_nonneg (show 0≤2*l-Real.sqrt 2 by linarith) (show 0≤2*l+Real.sqrt 2 by linarith)]
  · intro h
    nlinarith [mul_pos (show 0<Real.sqrt 2-2*l by linarith) (show 0<Real.sqrt 2+2*l by linarith)]
theorem carried_bound_iff (l : ℝ) (hl : 0≤l) :
    0<1-2*l-l^2 ↔ l<Real.sqrt 2-1 := by
  exact MutualCounterfeedingRegion.q_iff l hl
end InteractionTypology
