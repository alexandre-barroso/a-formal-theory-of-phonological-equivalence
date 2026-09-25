import PhonologicalOpacity.Attenuation.Productive.Subject.ProductiveSelection
import PhonologicalOpacity.Attenuation.Productive.Subject.FactsG34b
import PhonologicalOpacity.Attenuation.Productive.Subject.FactsG37c
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
theorem unique_fiber_G34b (s : List String) (hs : Generated rowsG34b s) (ho : observe s=outG34b) : s=goalG34b := by
  have h := fiberCheck_sound fiber_checked_G34b hs (by simpa using ho)
  simpa [goalsG34b,goalG34b] using h
theorem unique_fiber_G37c (s : List String) (hs : Generated rowsG37c s) (ho : observe s=outG37c) : s=goalG37c := by
  have h := fiberCheck_sound fiber_checked_G37c hs (by simpa using ho)
  simpa [goalsG37c,goalG37c] using h
theorem necessary_bound (w : Fin 9 → ℝ) (l : ℝ) (hw : 0≤w 4)
    (h34 : Exclusive rowsG34b (fullScore uG34b w l) outG34b)
    (h37 : Exclusive rowsG37c (fullScore uG37c w l) outG37c) : l<1/2 := by
  have ha := exclusive_strict h34 unique_fiber_G34b rival_generated_G34b rival_observed_G34b
  have hb := exclusive_strict h37 unique_fiber_G37c rival_generated_G37c rival_observed_G37c
  rw [goal_score_G34b,rival_score_G34b] at ha
  rw [goal_score_G37c,rival_score_G37c] at hb
  apply scalar_necessary (w 1) (w 4) l hw <;> nlinarith

#print axioms necessary_bound
end ProductiveSubjectGua
