                      
import PhonologicalCalculus.ContinuousHG.Heterogeneous

namespace PhonologicalCalculus.ContinuousHG.HeterogeneousObstruction

noncomputable def energy (a b c d e f : ℝ) : ℝ :=
  5*((max (1-a) 0)^2+(max (a-b) 0)^2+(max (b-c) 0)^2+
     (max (c-d) 0)^2+(max (d-e) 0)^2+(max (e-f) 0)^2)+a+b-4*c+d+e+f

theorem original_correspondence (a b c d e f : ℝ) :
    Heterogeneous.heteroHarmony 2 5 [1,1,-4,1,1,1] [a,b,c,d,e,f] = energy a b c d e f := by
  simp [Heterogeneous.heteroHarmony,directionalDrops,directionalDropsFrom,directionalDrop,realPowerPenalty,energy]
  ring

theorem drop_support (z v : ℝ) (hv : 0 ≤ v) :
    2*v*z-v^2 ≤ (max z 0)^2 := by
  have hz : z ≤ max z 0 := le_max_left _ _
  have hprod : 2*v*z ≤ 2*v*max z 0 := mul_le_mul_of_nonneg_left hz (by linarith)
  nlinarith [sq_nonneg (max z 0-v)]

theorem original_lower_bound (a b c d e f : ℝ) (hc : c ≤ 1) :
    1/20 ≤ energy a b c d e f := by
  have h1 := drop_support (1-a) (1/5) (by norm_num)
  have h2 := drop_support (a-b) (1/10) (by norm_num)
  have h3 := sq_nonneg (max (b-c) 0)
  have h4 := drop_support (c-d) (3/10) (by norm_num)
  have h5 := drop_support (d-e) (1/5) (by norm_num)
  have h6 := drop_support (e-f) (1/10) (by norm_num)
  unfold energy
  nlinarith

theorem original_minimum : energy (4/5) (7/10) 1 (7/10) (1/2) (2/5) = 1/20 := by
  norm_num [energy]

theorem monotone_lower_bound (a b c d e f : ℝ)
    (h1 : a ≤ 1) (h2 : b ≤ a) (h3 : c ≤ b)
    (h4 : d ≤ c) (h5 : e ≤ d) (h6 : f ≤ e) :
    1/4 ≤ energy a b c d e f := by
  have t1 := drop_support (1-a) (1/10) (by norm_num)
  have t2 := sq_nonneg (max (a-b) 0)
  have t3 := sq_nonneg (max (b-c) 0)
  have t4 := drop_support (c-d) (3/10) (by norm_num)
  have t5 := drop_support (d-e) (1/5) (by norm_num)
  have t6 := drop_support (e-f) (1/10) (by norm_num)
  unfold energy
  nlinarith

theorem monotone_minimum : energy (9/10) (9/10) (9/10) (3/5) (2/5) (3/10) = 1/4 := by
  norm_num [energy]

theorem continuous_obstruction :
    energy (4/5) (7/10) 1 (7/10) (1/2) (2/5) <
      energy (9/10) (9/10) (9/10) (3/5) (2/5) (3/10) := by
  rw [original_minimum,monotone_minimum]
  norm_num

end PhonologicalCalculus.ContinuousHG.HeterogeneousObstruction
