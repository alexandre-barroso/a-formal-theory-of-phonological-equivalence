import PhonologicalOpacity.Attenuation.Typology.Data
import PhonologicalOpacity.Attenuation.MutualCounterfeeding
namespace InteractionTypology
set_option maxHeartbeats 1000000 in
theorem region25 (l : ℝ) (hl : 0≤l) (hu : l≤1) :
    (∃w,Nonnegative w ∧ SystemHolds system25 w l) ↔ (0 < 1-2*l^2) := by
  constructor
  · rintro ⟨⟨w0,w1,w2,w3,w4,w5,w6,w7,w8⟩,hw,hs⟩
    rcases hw with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
    norm_num [SystemHolds,system25,evalDelta,dotInt,values] at hs
    repeat' (first | (rcases hs with ⟨hh,hs⟩) | (rcases hs with hs | hs))
    all_goals
      have ha : 0 < w0+w2-2*l*w3 := by linarith
      have hb : 0 < w3-l*w0-w2 := by linarith
      have hp : 0 < (1-2*l^2)*w3 := by
        nlinarith [mul_nonneg hl (le_of_lt ha),mul_nonneg (sub_nonneg.mpr hu) h2]
      by_contra hn
      have hq : 1-2*l^2≤0 := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hq h3)) hp
  · intro h
    have hsmall : l < 3/4 := by nlinarith
    have ha := mul_nonneg hl (sq_nonneg (1-l))
    have hb := mul_nonneg hl (sq_nonneg l)
    have hc := mul_nonneg (sq_nonneg l) (show 0≤3/4-l by linarith)
    refine ⟨⟨2*l+(1-2*l^2),l+(1-2*l^2)/2,(1-2*l^2)/4,1,0,0,0,0,0⟩,?_,?_⟩
    · norm_num [Nonnegative] <;> (repeat' constructor) <;> nlinarith [sq_nonneg l]
    · norm_num [SystemHolds,system25,evalDelta,dotInt,values]
      all_goals try simp only [abs_of_nonneg hl]
      all_goals (repeat' constructor) <;> nlinarith [sq_nonneg l]
end InteractionTypology
