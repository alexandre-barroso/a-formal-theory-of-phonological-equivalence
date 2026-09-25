import PhonologicalOpacity.Gua.Core
namespace Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem full_C24ei : complete c24 63 16 = true := by decide
theorem fiber_C24ei : fiber c24 "kpejsi" = [63] := by decide
theorem start_C24ei : expand c24 58 = c24.origin := by decide
theorem selects_C24ei (mode : Nat) (hm : mode ∈ [0,1]) :
    UniqueMin c24 (score8 c24 mode) 63 :=
  complete_unique full_C24ei (by decide) hm
theorem observed_C24ei (mode i : Nat) (hm : mode ∈ [0,1])
    (hi : i ∈ carrier c24)
    (hmin : ∀ j ∈ carrier c24, score8 c24 mode i ≤ score8 c24 mode j) :
    realize c24 i = "kpejsi" := by
  have h := unique_min_observation (selects_C24ei mode hm) hi hmin
  exact h.trans (by decide)
#print axioms full_C24ei
#print axioms fiber_C24ei
#print axioms selects_C24ei
#print axioms observed_C24ei
end Retained
