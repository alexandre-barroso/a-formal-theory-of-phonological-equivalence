import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c00
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c01
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c02
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c03
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c04
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c05
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c06
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c07
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c08
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c09
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c10
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c11
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c12
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem certificate_D0G37c_1 : checkAll g37 1 [1584] 28 = true := by
  apply assembleBlocks (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_D0G37c_1_0
  · exact block_D0G37c_1_1
  · exact block_D0G37c_1_2
  · exact block_D0G37c_1_3
  · exact block_D0G37c_1_4
  · exact block_D0G37c_1_5
  · exact block_D0G37c_1_6
  · exact block_D0G37c_1_7
  · exact block_D0G37c_1_8
  · exact block_D0G37c_1_9
  · exact block_D0G37c_1_10
  · exact block_D0G37c_1_11
  · exact block_D0G37c_1_12
theorem minima_D0G37c_1 (i : Nat) (hi : i ∈ carrier g37) :
    (∀ j ∈ carrier g37, score g37 1 i ≤ score g37 1 j) ↔ i ∈ [1584] :=
  certificate_minima certificate_D0G37c_1 (by decide) (by decide) i hi
#print axioms certificate_D0G37c_1
#print axioms minima_D0G37c_1
end Deletion
