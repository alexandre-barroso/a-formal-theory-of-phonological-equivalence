import PhonologicalOpacity.Gua.Blocks.G34b00
import PhonologicalOpacity.Gua.Blocks.G34b01
import PhonologicalOpacity.Gua.Blocks.G34b02
import PhonologicalOpacity.Gua.Blocks.G34b03
import PhonologicalOpacity.Gua.Blocks.G34b04
import PhonologicalOpacity.Gua.Blocks.G34b05
import PhonologicalOpacity.Gua.Blocks.G34b06
import PhonologicalOpacity.Gua.Blocks.G34b07
import PhonologicalOpacity.Gua.Blocks.G34b08
import PhonologicalOpacity.Gua.Blocks.G34b09
import PhonologicalOpacity.Gua.Blocks.G34b10
import PhonologicalOpacity.Gua.Blocks.G34b11
import PhonologicalOpacity.Gua.Blocks.G34b12
namespace Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem full_G34b : complete g34b 957 20 = true := by
  apply assemble_blocks (u := g34b) (goal := 957) (expected := 20) (by decide)
  intro b hb
  interval_cases b
  · exact block_G34b_0
  · exact block_G34b_1
  · exact block_G34b_2
  · exact block_G34b_3
  · exact block_G34b_4
  · exact block_G34b_5
  · exact block_G34b_6
  · exact block_G34b_7
  · exact block_G34b_8
  · exact block_G34b_9
  · exact block_G34b_10
  · exact block_G34b_11
  · exact block_G34b_12
theorem fiber_G34b : fiber g34b "afɪsoohili" = [957] := by decide
theorem start_G34b : expand g34b 892 = g34b.origin := by decide
theorem selects_G34b (mode : Nat) (hm : mode ∈ [0,1]) :
    UniqueMin g34b (score8 g34b mode) 957 :=
  complete_unique full_G34b (by decide) hm
theorem observed_G34b (mode i : Nat) (hm : mode ∈ [0,1])
    (hi : i ∈ carrier g34b)
    (hmin : ∀ j ∈ carrier g34b, score8 g34b mode i ≤ score8 g34b mode j) :
    realize g34b i = "afɪsoohili" := by
  have h := unique_min_observation (selects_G34b mode hm) hi hmin
  exact h.trans (by decide)
#print axioms full_G34b
#print axioms fiber_G34b
#print axioms selects_G34b
#print axioms observed_G34b
end Retained
