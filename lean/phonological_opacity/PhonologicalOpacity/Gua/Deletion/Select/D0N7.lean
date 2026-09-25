import PhonologicalOpacity.Gua.Deletion.Blocks.D0N700
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_D0N7_1 : checkAll n7 1 [82] 8 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_D0N7_1_0
theorem minima_D0N7_1 (i : Nat) (hi : i ∈ carrier n7) :
    (∀ j ∈ carrier n7, score n7 1 i ≤ score n7 1 j) ↔ i ∈ [82] :=
  certificate_minima certificate_D0N7_1 (by decide) (by decide) i hi
#print axioms certificate_D0N7_1
#print axioms minima_D0N7_1
end Deletion
