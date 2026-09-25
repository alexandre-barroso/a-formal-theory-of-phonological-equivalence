import PhonologicalOpacity.Gua.Deletion.Blocks.OR3800
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3801
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3802
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3803
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3804
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3805
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3806
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3807
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3808
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3809
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3810
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3811
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3812
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_OR38_0 : checkAll or38 0 [1261] 172 = true := by
  apply assembleBlocks (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_OR38_0_0
  · exact block_OR38_0_1
  · exact block_OR38_0_2
  · exact block_OR38_0_3
  · exact block_OR38_0_4
  · exact block_OR38_0_5
  · exact block_OR38_0_6
  · exact block_OR38_0_7
  · exact block_OR38_0_8
  · exact block_OR38_0_9
  · exact block_OR38_0_10
  · exact block_OR38_0_11
  · exact block_OR38_0_12
theorem minima_OR38_0 (i : Nat) (hi : i ∈ carrier or38) :
    (∀ j ∈ carrier or38, score or38 0 i ≤ score or38 0 j) ↔ i ∈ [1261] :=
  certificate_minima certificate_OR38_0 (by decide) (by decide) i hi
#print axioms certificate_OR38_0
#print axioms minima_OR38_0
theorem certificate_OR38_1 : checkAll or38 1 [1267] 12 = true := by
  apply assembleBlocks (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_OR38_1_0
  · exact block_OR38_1_1
  · exact block_OR38_1_2
  · exact block_OR38_1_3
  · exact block_OR38_1_4
  · exact block_OR38_1_5
  · exact block_OR38_1_6
  · exact block_OR38_1_7
  · exact block_OR38_1_8
  · exact block_OR38_1_9
  · exact block_OR38_1_10
  · exact block_OR38_1_11
  · exact block_OR38_1_12
theorem minima_OR38_1 (i : Nat) (hi : i ∈ carrier or38) :
    (∀ j ∈ carrier or38, score or38 1 i ≤ score or38 1 j) ↔ i ∈ [1267] :=
  certificate_minima certificate_OR38_1 (by decide) (by decide) i hi
#print axioms certificate_OR38_1
#print axioms minima_OR38_1
theorem certificate_OR38_2 : checkAll or38 2 [1332] 20 = true := by
  apply assembleBlocks (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_OR38_2_0
  · exact block_OR38_2_1
  · exact block_OR38_2_2
  · exact block_OR38_2_3
  · exact block_OR38_2_4
  · exact block_OR38_2_5
  · exact block_OR38_2_6
  · exact block_OR38_2_7
  · exact block_OR38_2_8
  · exact block_OR38_2_9
  · exact block_OR38_2_10
  · exact block_OR38_2_11
  · exact block_OR38_2_12
theorem minima_OR38_2 (i : Nat) (hi : i ∈ carrier or38) :
    (∀ j ∈ carrier or38, score or38 2 i ≤ score or38 2 j) ↔ i ∈ [1332] :=
  certificate_minima certificate_OR38_2 (by decide) (by decide) i hi
#print axioms certificate_OR38_2
#print axioms minima_OR38_2
end Deletion
