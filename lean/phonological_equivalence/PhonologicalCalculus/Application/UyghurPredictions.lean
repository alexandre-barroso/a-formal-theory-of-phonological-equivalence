import PhonologicalCalculus.Application.UyghurJoint
import PhonologicalCalculus.MaxEnt.SlovenianRetention

namespace UyghurPredictions
open UyghurJoint
noncomputable section

abbrev Candidate := Bool × Bool

def score (H lam L R : ℝ) (previous old : Bool) (c : Candidate) : ℝ :=
  nativeScore H lam L R previous old c.1 c.2

def partition (e : Candidate → ℝ) : ℝ := ∑ c, Real.exp (-e c)

theorem partition_pos (e : Candidate → ℝ) : 0 < partition e := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem probability_ratio (e : Candidate → ℝ) (c d : Candidate) :
    SlovenianRetention.probability e c / SlovenianRetention.probability e d =
      Real.exp (-(e c - e d)) := by
  have hz : (∑ x, Real.exp (-e x)) ≠ 0 := ne_of_gt (partition_pos e)
  simp only [SlovenianRetention.probability]
  rw [div_div_div_cancel_right₀ hz, ← Real.exp_sub]
  congr 1
  ring

theorem opposite_suffix_gap (H lam L R : ℝ) (previous old : Bool) :
    score H lam L R previous old (true, !old) -
      score H lam L R previous old (false, !old) = R-L := by
  simp only [score, complete_score]
  cases previous <;> cases old <;> simp [normalScore] <;> ring

theorem opposite_suffix_raising_odds (H lam L R : ℝ) (previous old : Bool) :
    SlovenianRetention.probability (score H lam L R previous old) (true,!old) /
      SlovenianRetention.probability (score H lam L R previous old) (false,!old) =
        Real.exp (-(R-L)) := by
  rw [probability_ratio, opposite_suffix_gap]

def raisingFactor (A B : ℝ) : ℝ :=
  (Real.exp (-B) + Real.exp (-A)) / (1 + Real.exp (-A))

theorem raisingFactor_pos (A B : ℝ) : 0 < raisingFactor A B := by
  unfold raisingFactor
  exact div_pos (add_pos (Real.exp_pos _) (Real.exp_pos _)) (by positivity)

theorem raisingFactor_le_one (A B : ℝ) (hB : 0 ≤ B) : raisingFactor A B ≤ 1 := by
  unfold raisingFactor
  apply (div_le_one (by positivity : (0:ℝ) < 1 + Real.exp (-A))).2
  have h : Real.exp (-B) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem raisingFactor_eq_one_iff (A B : ℝ) : raisingFactor A B = 1 ↔ B = 0 := by
  unfold raisingFactor
  rw [div_eq_one_iff_eq (by positivity : (1:ℝ)+Real.exp (-A) ≠ 0)]
  constructor
  · intro h
    have : Real.exp (-B) = 1 := by linarith
    have : -B = 0 := by simpa using this
    linarith
  · intro h
    simp [h]

theorem carrier_card : Fintype.card Candidate = 4 := by decide

end
end UyghurPredictions
