import PhonologicalOpacity.Attenuation.Typology.Data
import PhonologicalOpacity.Attenuation.MutualCounterfeeding
namespace InteractionTypology
set_option maxHeartbeats 1000000 in
theorem region6 (l : ℝ) (hl : 0≤l) (hu : l≤1) :
    (∃w,Nonnegative w ∧ SystemHolds system6 w l) ↔ (True) := by
  constructor
  · rintro ⟨⟨w0,w1,w2,w3,w4,w5,w6,w7,w8⟩,hw,hs⟩
    rcases hw with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
    norm_num [SystemHolds,system6,evalDelta,dotInt,values] at hs
    repeat' (first | (rcases hs with ⟨hh,hs⟩) | (rcases hs with hs | hs))
    all_goals trivial
  · intro h
    refine ⟨⟨(1/1),(2/1),(2/1),(3/1),0,0,0,0,0⟩,?_,?_⟩
    · norm_num [Nonnegative] <;> (repeat' constructor) <;> nlinarith [sq_nonneg l]
    · norm_num [SystemHolds,system6,evalDelta,dotInt,values]
      all_goals try simp only [abs_of_nonneg hl]
      all_goals (repeat' constructor) <;> nlinarith [sq_nonneg l]
end InteractionTypology
