import PhonologicalOpacity.Attenuation.Lardil
import PhonologicalOpacity.Attenuation.MutualCounterfeeding
import PhonologicalOpacity.Attenuation.Typology.Region00
namespace InteractionObstruction
theorem lardil_scalar_no_go (S : Set ℝ) (sub : Bool)
    (h : ∃ l ∈ S, 0≤l ∧ ∃ ma mk w,
      LardilRegion.Nonnegative w ∧ LardilRegion.FullSelection ma mk sub l w) :
    ∃ l ∈ S, 0≤l ∧ ∃w,MutualCounterfeedingRegion.Nonnegative w ∧
      MutualCounterfeedingRegion.FullSelection (false,false) (false,false) l w := by
  obtain ⟨l,hs,hl,ma,mk,w,hw,hj⟩ := h
  have hb := (LardilRegion.full_exact_region ma mk sub l hl).mp ⟨w,hw,hj⟩
  refine ⟨l,hs,hl,?_⟩
  exact (MutualCounterfeedingRegion.full_exact_region (false,false) (false,false) l hl).mpr (by simpa using hb.2.2)
theorem counterfeeding_projection_strict :
    (∃w,InteractionTypology.Nonnegative w ∧ InteractionTypology.SystemHolds
      InteractionTypology.system0 w (3/4)) ∧
    ¬(∃w,MutualCounterfeedingRegion.Nonnegative w ∧
      MutualCounterfeedingRegion.FullSelection (false,false) (false,false) (3/4) w) := by
  constructor
  · exact (InteractionTypology.region0 (3/4) (by norm_num) (by norm_num)).mpr (by norm_num)
  · rw [MutualCounterfeedingRegion.full_exact_region (false,false) (false,false) (3/4) (by norm_num)]
    norm_num
end InteractionObstruction
