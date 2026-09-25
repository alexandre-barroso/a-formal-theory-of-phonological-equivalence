import PhonologicalOpacity.Gua.Deletion.Blocks.C21b00
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_C21b_0 : checkAll c21 0 [117] 160 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C21b_0_0
theorem minima_C21b_0 (i : Nat) (hi : i ∈ carrier c21) :
    (∀ j ∈ carrier c21, score c21 0 i ≤ score c21 0 j) ↔ i ∈ [117] :=
  certificate_minima certificate_C21b_0 (by decide) (by decide) i hi
#print axioms certificate_C21b_0
#print axioms minima_C21b_0
theorem certificate_C21b_1 : checkAll c21 1 [122] 0 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C21b_1_0
theorem minima_C21b_1 (i : Nat) (hi : i ∈ carrier c21) :
    (∀ j ∈ carrier c21, score c21 1 i ≤ score c21 1 j) ↔ i ∈ [122] :=
  certificate_minima certificate_C21b_1 (by decide) (by decide) i hi
#print axioms certificate_C21b_1
#print axioms minima_C21b_1
theorem certificate_C21b_2 : checkAll c21 2 [18,44,96,128,161] 16 = true := by
  apply assembleBlocks (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C21b_2_0
theorem minima_C21b_2 (i : Nat) (hi : i ∈ carrier c21) :
    (∀ j ∈ carrier c21, score c21 2 i ≤ score c21 2 j) ↔ i ∈ [18,44,96,128,161] :=
  certificate_minima certificate_C21b_2 (by decide) (by decide) i hi
#print axioms certificate_C21b_2
#print axioms minima_C21b_2
end Deletion
