import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a00
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a01
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a02
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a03
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a04
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a05
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a06
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a07
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a08
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a09
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a10
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a11
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a12
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_D0G34a_1 : checkAll g34a 1 [774] 24 = true := by
  apply assembleBlocks (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_D0G34a_1_0
  · exact block_D0G34a_1_1
  · exact block_D0G34a_1_2
  · exact block_D0G34a_1_3
  · exact block_D0G34a_1_4
  · exact block_D0G34a_1_5
  · exact block_D0G34a_1_6
  · exact block_D0G34a_1_7
  · exact block_D0G34a_1_8
  · exact block_D0G34a_1_9
  · exact block_D0G34a_1_10
  · exact block_D0G34a_1_11
  · exact block_D0G34a_1_12
theorem minima_D0G34a_1 (i : Nat) (hi : i ∈ carrier g34a) :
    (∀ j ∈ carrier g34a, score g34a 1 i ≤ score g34a 1 j) ↔ i ∈ [774] :=
  certificate_minima certificate_D0G34a_1 (by decide) (by decide) i hi
#print axioms certificate_D0G34a_1
#print axioms minima_D0G34a_1
end Deletion
