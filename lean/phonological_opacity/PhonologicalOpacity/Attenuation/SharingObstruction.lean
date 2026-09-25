import PhonologicalOpacity.Attenuation.FreeWeights.SubjectComplete
import PhonologicalOpacity.Attenuation.MutualCounterfeeding
namespace AttenuationSharing

theorem scalar_restriction_no_go (S : Set ℝ)
    (h : ∃ l ∈ S, 0 ≤ l ∧ ∃ w : Fin 9 → ℝ, (∀ k, 0 ≤ w k) ∧ FreeWeights.SubjectJoint w l) :
    ∃ l ∈ S, 0 ≤ l ∧ ∃ w : MutualCounterfeedingRegion.Weights,
      MutualCounterfeedingRegion.Nonnegative w ∧
      MutualCounterfeedingRegion.FullSelection (false,false) (false,false) l w := by
  obtain ⟨l,hS,hl,w,hw,hj⟩ := h
  have hb : l < 1/2 := (FreeWeights.subject_exact_region l hl).1 ⟨w,hw,hj⟩
  refine ⟨l,hS,hl,?_⟩
  exact (MutualCounterfeedingRegion.full_exact_region (false,false) (false,false) l hl).2 (by simpa using hb)
end AttenuationSharing
