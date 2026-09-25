import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b00
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b01
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b02
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b03
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b04
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b05
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b06
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b07
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b08
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b09
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b10
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b11
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b12
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_D0G34b_1 : checkAll g34b 1 [957] 20 = true := by
  apply assembleBlocks (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_D0G34b_1_0
  · exact block_D0G34b_1_1
  · exact block_D0G34b_1_2
  · exact block_D0G34b_1_3
  · exact block_D0G34b_1_4
  · exact block_D0G34b_1_5
  · exact block_D0G34b_1_6
  · exact block_D0G34b_1_7
  · exact block_D0G34b_1_8
  · exact block_D0G34b_1_9
  · exact block_D0G34b_1_10
  · exact block_D0G34b_1_11
  · exact block_D0G34b_1_12
theorem minima_D0G34b_1 (i : Nat) (hi : i ∈ carrier g34b) :
    (∀ j ∈ carrier g34b, score g34b 1 i ≤ score g34b 1 j) ↔ i ∈ [957] :=
  certificate_minima certificate_D0G34b_1 (by decide) (by decide) i hi
#print axioms certificate_D0G34b_1
#print axioms minima_D0G34b_1
end Deletion
