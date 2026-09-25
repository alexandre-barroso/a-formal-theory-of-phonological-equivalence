import PhonologicalOpacity.Gua.Blocks.G34a00
import PhonologicalOpacity.Gua.Blocks.G34a01
import PhonologicalOpacity.Gua.Blocks.G34a02
import PhonologicalOpacity.Gua.Blocks.G34a03
import PhonologicalOpacity.Gua.Blocks.G34a04
import PhonologicalOpacity.Gua.Blocks.G34a05
import PhonologicalOpacity.Gua.Blocks.G34a06
import PhonologicalOpacity.Gua.Blocks.G34a07
import PhonologicalOpacity.Gua.Blocks.G34a08
import PhonologicalOpacity.Gua.Blocks.G34a09
import PhonologicalOpacity.Gua.Blocks.G34a10
import PhonologicalOpacity.Gua.Blocks.G34a11
import PhonologicalOpacity.Gua.Blocks.G34a12
namespace Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem full_G34a : complete g34a 774 24 = true := by
  apply assemble_blocks (u := g34a) (goal := 774) (expected := 24) (by decide)
  intro b hb
  interval_cases b
  · exact block_G34a_0
  · exact block_G34a_1
  · exact block_G34a_2
  · exact block_G34a_3
  · exact block_G34a_4
  · exact block_G34a_5
  · exact block_G34a_6
  · exact block_G34a_7
  · exact block_G34a_8
  · exact block_G34a_9
  · exact block_G34a_10
  · exact block_G34a_11
  · exact block_G34a_12
theorem fiber_G34a : fiber g34a "ahetɔɔkpʊkɔ" = [774] := by decide
theorem start_G34a : expand g34a 566 = g34a.origin := by decide
theorem selects_G34a (mode : Nat) (hm : mode ∈ [0,1]) :
    UniqueMin g34a (score8 g34a mode) 774 :=
  complete_unique full_G34a (by decide) hm
theorem observed_G34a (mode i : Nat) (hm : mode ∈ [0,1])
    (hi : i ∈ carrier g34a)
    (hmin : ∀ j ∈ carrier g34a, score8 g34a mode i ≤ score8 g34a mode j) :
    realize g34a i = "ahetɔɔkpʊkɔ" := by
  have h := unique_min_observation (selects_G34a mode hm) hi hmin
  exact h.trans (by decide)
#print axioms full_G34a
#print axioms fiber_G34a
#print axioms selects_G34a
#print axioms observed_G34a
end Retained
