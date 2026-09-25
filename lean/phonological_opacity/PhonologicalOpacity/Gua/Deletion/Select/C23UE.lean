import PhonologicalOpacity.Gua.Deletion.Blocks.C23UE00
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_C23UE_0 : checkAll c23 0 [159] 16 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C23UE_0_0
theorem minima_C23UE_0 (i : Nat) (hi : i ∈ carrier c23) :
    (∀ j ∈ carrier c23, score c23 0 i ≤ score c23 0 j) ↔ i ∈ [159] :=
  certificate_minima certificate_C23UE_0 (by decide) (by decide) i hi
#print axioms certificate_C23UE_0
#print axioms minima_C23UE_0
theorem certificate_C23UE_1 : checkAll c23 1 [159] 16 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C23UE_1_0
theorem minima_C23UE_1 (i : Nat) (hi : i ∈ carrier c23) :
    (∀ j ∈ carrier c23, score c23 1 i ≤ score c23 1 j) ↔ i ∈ [159] :=
  certificate_minima certificate_C23UE_1 (by decide) (by decide) i hi
#print axioms certificate_C23UE_1
#print axioms minima_C23UE_1
theorem certificate_C23UE_2 : checkAll c23 2 [159] 16 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C23UE_2_0
theorem minima_C23UE_2 (i : Nat) (hi : i ∈ carrier c23) :
    (∀ j ∈ carrier c23, score c23 2 i ≤ score c23 2 j) ↔ i ∈ [159] :=
  certificate_minima certificate_C23UE_2 (by decide) (by decide) i hi
#print axioms certificate_C23UE_2
#print axioms minima_C23UE_2
end Deletion
