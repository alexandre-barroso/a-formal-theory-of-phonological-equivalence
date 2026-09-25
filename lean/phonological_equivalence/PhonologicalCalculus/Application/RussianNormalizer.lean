                                 
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace RussianNormalizer

noncomputable def firstProbability (a b c d : ℝ) : ℝ :=
  Real.exp (-a) / (Real.exp (-a) + Real.exp (-b) + Real.exp (-c) + Real.exp (-d))

theorem centered (a b c d : ℝ) :
    firstProbability a b c d =
      1 / (1 + Real.exp (a-b) + Real.exp (a-c) + Real.exp (a-d)) := by
  have hb : Real.exp (-b) = Real.exp (-a) * Real.exp (a-b) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc : Real.exp (-c) = Real.exp (-a) * Real.exp (a-c) := by
    rw [← Real.exp_add]; congr 1; ring
  have hd : Real.exp (-d) = Real.exp (-a) * Real.exp (a-d) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold firstProbability
  rw [hb,hc,hd]
  rw [show Real.exp (-a) + Real.exp (-a)*Real.exp (a-b) +
      Real.exp (-a)*Real.exp (a-c) + Real.exp (-a)*Real.exp (a-d) =
      Real.exp (-a)*(1+Real.exp (a-b)+Real.exp (a-c)+Real.exp (a-d)) by ring]
  rw [div_mul_eq_div_div,div_self (Real.exp_ne_zero _)]

theorem displayed_contrast_equal :
    (129/40 - 1/5 : ℝ) = 123/40 - 1/20 ∧
    (49/40 - 1/5 : ℝ) = 43/40 - 1/20 := by norm_num

theorem first_probability_strict :
    firstProbability (1/5) (49/40) (49/20) (129/40) <
      firstProbability (1/20) (43/40) (19/8) (123/40) := by
  rw [centered,centered]
  norm_num
  have he : Real.exp (-93/40 : ℝ) < Real.exp (-9/4 : ℝ) := by
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hp : 0 < (1 + Real.exp (-41/40) + Real.exp (-93/40) + Real.exp (-121/40) : ℝ) := by positivity
  have hd : (1 + Real.exp (-41/40) + Real.exp (-93/40) + Real.exp (-121/40) : ℝ) <
      1 + Real.exp (-41/40) + Real.exp (-9/4) + Real.exp (-121/40) := by linarith
  simpa only [one_div,neg_div] using one_div_lt_one_div_of_lt hp hd

end RussianNormalizer
