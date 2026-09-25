import PhonologicalOpacity.Attenuation.Typology.Data
import PhonologicalOpacity.Attenuation.MutualCounterfeeding
namespace InteractionTypology
set_option maxHeartbeats 1000000 in
theorem region26 (l : ℝ) (hl : 0≤l) (hu : l≤1) :
    (∃w,Nonnegative w ∧ SystemHolds system26 w l) ↔ (False) := by
  constructor
  · rintro ⟨⟨w0,w1,w2,w3,w4,w5,w6,w7,w8⟩,hw,hs⟩
    rcases hw with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
    norm_num [SystemHolds,system26,evalDelta,dotInt,values] at hs
    repeat' (first | (rcases hs with ⟨hh,hs⟩) | (rcases hs with hs | hs))
    all_goals linarith
  · intro h;exact False.elim h
end InteractionTypology
