import PhonologicalOpacity.Gua.Core
namespace Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem full_N7 : complete n7 82 8 = true := by decide
theorem fiber_N7 : fiber n7 "atʃijeli" = [82] := by decide
theorem start_N7 : expand n7 69 = n7.origin := by decide
theorem selects_N7 (mode : Nat) (hm : mode ∈ [0,1]) :
    UniqueMin n7 (score8 n7 mode) 82 :=
  complete_unique full_N7 (by decide) hm
theorem observed_N7 (mode i : Nat) (hm : mode ∈ [0,1])
    (hi : i ∈ carrier n7)
    (hmin : ∀ j ∈ carrier n7, score8 n7 mode i ≤ score8 n7 mode j) :
    realize n7 i = "atʃijeli" := by
  have h := unique_min_observation (selects_N7 mode hm) hi hmin
  exact h.trans (by decide)
#print axioms full_N7
#print axioms fiber_N7
#print axioms selects_N7
#print axioms observed_N7
end Retained
