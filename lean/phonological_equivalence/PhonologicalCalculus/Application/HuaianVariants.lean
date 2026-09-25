                       
import PhonologicalCalculus.Application.HuaianOdds

namespace HuaianOdds
noncomputable section

def targetMarked (u un v vn : Tone) (l : ℝ) : ℝ :=
  (if u = 2 ∧ un = 2 then 1 else if v = 2 ∧ vn = 2 then l else 0) *
  (if v ≠ 1 then 1 else 0)

def scoreB (u v : Triple) (w : Weights) (l : ℝ) : ℝ :=
  score u v w l + w.s33 *
  (targetMarked (u 0) (u 1) (v 0) (v 1) l +
   targetMarked (u 1) (u 2) (v 1) (v 2) l -
   marked (u 0) (u 1) (v 0) (v 1) 2 1 l -
   marked (u 1) (u 2) (v 1) (v 2) 2 1 l)

def marked32 (u un v vn : Tone) (l : ℝ) : ℝ :=
  (if u = 2 ∧ un = 1 then 1 else if v = 2 ∧ vn = 1 then l else 0) *
  (if vn = 1 ∧ v ≠ 1 then 1 else 0)

def scoreC (u v : Triple) (w : Weights) (l k : ℝ) : ℝ :=
  score u v w l + k *
   (marked32 (u 0) (u 1) (v 0) (v 1) l +
    marked32 (u 1) (u 2) (v 1) (v 2) l)

def u323 : Triple := ![2, 1, 2]

theorem gapA323 (w : Weights) (l : ℝ) :
    score u323 v223 w l - score u323 v323 w l = w.cont := by
  norm_num [score, marked, u323, v223, v323, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

theorem gapB333 (w : Weights) (l : ℝ) :
    scoreB u333 v223 w l - scoreB u333 v323 w l = w.cont - w.s33 := by
  simp only [scoreB, score_223, score_323]
  norm_num [targetMarked, marked, u333, v223, v323, Fin.ext_iff]
  ring

theorem gapB323 (w : Weights) (l : ℝ) :
    scoreB u323 v223 w l - scoreB u323 v323 w l = w.cont := by
  have h := gapA323 w l
  simp only [scoreB]
  norm_num [targetMarked, marked, u323, v223, v323, Fin.ext_iff]
  exact h

theorem gapC333 (w : Weights) (l k : ℝ) :
    scoreC u333 v223 w l k - scoreC u333 v323 w l k = w.cont - l*k := by
  simp only [scoreC, score_223, score_323]
  norm_num [marked32, u333, v223, v323, Fin.ext_iff]
  ring

theorem gapC323 (w : Weights) (l k : ℝ) :
    scoreC u323 v223 w l k - scoreC u323 v323 w l k = w.cont - k := by
  have h := gapA323 w l
  simp only [u323, v223, v323] at h
  simp only [scoreC]
  norm_num [marked32, u323, v223, v323, Fin.ext_iff]
  linarith

theorem B_gap_order (w : Weights) (l : ℝ) (h : 0 ≤ w.s33) :
    scoreB u333 v223 w l - scoreB u333 v323 w l ≤
    scoreB u323 v223 w l - scoreB u323 v323 w l := by
  rw [gapB333, gapB323]
  linarith

theorem C_gap_order (w : Weights) (l k : ℝ) (hl : l ≤ 1) (hk : 0 ≤ k) :
    scoreC u323 v223 w l k - scoreC u323 v323 w l k ≤
    scoreC u333 v223 w l k - scoreC u333 v323 w l k := by
  rw [gapC333, gapC323]
  nlinarith

def conditional (a b : ℝ) : ℝ := Real.exp (-a) / (Real.exp (-a) + Real.exp (-b))

theorem conditional_formula (a b : ℝ) :
    conditional a b = 1 / (1 + Real.exp (a-b)) := by
  have ha : Real.exp (-a) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have h : Real.exp (-b) = Real.exp (-a) * Real.exp (a-b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold conditional
  rw [h]
  field_simp

theorem conditional_gap_antitone (a b c d : ℝ) (h : a-b ≤ c-d) :
    conditional c d ≤ conditional a b := by
  rw [conditional_formula, conditional_formula]
  exact one_div_le_one_div_of_le (by positivity) (by gcongr)

theorem B_conditional_order (w : Weights) (l : ℝ) (h : 0 ≤ w.s33) :
    conditional (scoreB u323 v223 w l) (scoreB u323 v323 w l) ≤
    conditional (scoreB u333 v223 w l) (scoreB u333 v323 w l) := by
  exact conditional_gap_antitone _ _ _ _ (B_gap_order w l h)

theorem C_conditional_order (w : Weights) (l k : ℝ) (hl : l ≤ 1) (hk : 0 ≤ k) :
    conditional (scoreC u333 v223 w l k) (scoreC u333 v323 w l k) ≤
    conditional (scoreC u323 v223 w l k) (scoreC u323 v323 w l k) := by
  exact conditional_gap_antitone _ _ _ _ (C_gap_order w l k hl hk)

end
end HuaianOdds
