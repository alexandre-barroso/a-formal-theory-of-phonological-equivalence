import PhonologicalOpacity.Gua.Deletion.Blocks.D0C2400
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_D0C24_1 : checkAll c24 1 [63] 16 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_D0C24_1_0
theorem minima_D0C24_1 (i : Nat) (hi : i ∈ carrier c24) :
    (∀ j ∈ carrier c24, score c24 1 i ≤ score c24 1 j) ↔ i ∈ [63] :=
  certificate_minima certificate_D0C24_1 (by decide) (by decide) i hi
#print axioms certificate_D0C24_1
#print axioms minima_D0C24_1
end Deletion
