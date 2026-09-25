import PhonologicalOpacity.Attenuation.Typology.Data
import PhonologicalOpacity.Attenuation.MutualCounterfeeding
namespace InteractionTypology
set_option maxHeartbeats 1000000 in
theorem region24 (l : ℝ) (hl : 0≤l) (hu : l≤1) :
    (∃w,Nonnegative w ∧ SystemHolds system24 w l) ↔ (0 < l ∧ l < 1/2) := by
  constructor
  · rintro ⟨⟨w0,w1,w2,w3,w4,w5,w6,w7,w8⟩,hw,hs⟩
    rcases hw with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
    norm_num [SystemHolds,system24,evalDelta,dotInt,values] at hs
    repeat' (first | (rcases hs with ⟨hh,hs⟩) | (rcases hs with hs | hs))
    all_goals constructor
    · by_contra hn
      have hz : l=0 := by linarith
      subst l
      norm_num at *
      linarith
    · by_contra hn
      have he : 0≤2*l-1 := by linarith
      nlinarith [mul_nonneg he h0,mul_nonneg he h1,mul_nonneg he h2,mul_nonneg he h3,mul_nonneg he h4,mul_nonneg he h5,mul_nonneg he h6,mul_nonneg he h7,mul_nonneg he h8]
  · intro h
    rcases h with ⟨hpos,hupper⟩
    refine ⟨⟨(4/1),(8/1),0,(2/1),0,0,0,0,0⟩,?_,?_⟩
    · norm_num [Nonnegative] <;> (repeat' constructor) <;> nlinarith [sq_nonneg l]
    · norm_num [SystemHolds,system24,evalDelta,dotInt,values]
      try left
      all_goals try simp only [abs_of_nonneg hl]
      all_goals (repeat' constructor) <;> nlinarith [sq_nonneg l]
end InteractionTypology
