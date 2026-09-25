import PhonologicalOpacity.Gua.Blocks.G37c00
import PhonologicalOpacity.Gua.Blocks.G37c01
import PhonologicalOpacity.Gua.Blocks.G37c02
import PhonologicalOpacity.Gua.Blocks.G37c03
import PhonologicalOpacity.Gua.Blocks.G37c04
import PhonologicalOpacity.Gua.Blocks.G37c05
import PhonologicalOpacity.Gua.Blocks.G37c06
import PhonologicalOpacity.Gua.Blocks.G37c07
import PhonologicalOpacity.Gua.Blocks.G37c08
import PhonologicalOpacity.Gua.Blocks.G37c09
import PhonologicalOpacity.Gua.Blocks.G37c10
import PhonologicalOpacity.Gua.Blocks.G37c11
import PhonologicalOpacity.Gua.Blocks.G37c12
namespace Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem full_G37c : complete g37 1584 28 = true := by
  apply assemble_blocks (u := g37) (goal := 1584) (expected := 28) (by decide)
  intro b hb
  interval_cases b
  · exact block_G37c_0
  · exact block_G37c_1
  · exact block_G37c_2
  · exact block_G37c_3
  · exact block_G37c_4
  · exact block_G37c_5
  · exact block_G37c_6
  · exact block_G37c_7
  · exact block_G37c_8
  · exact block_G37c_9
  · exact block_G37c_10
  · exact block_G37c_11
  · exact block_G37c_12
theorem fiber_G37c : fiber g37 "ɔtʃʊsejbie" = [1584] := by decide
theorem start_G37c : expand g37 1566 = g37.origin := by decide
theorem selects_G37c (mode : Nat) (hm : mode ∈ [0,1]) :
    UniqueMin g37 (score8 g37 mode) 1584 :=
  complete_unique full_G37c (by decide) hm
theorem observed_G37c (mode i : Nat) (hm : mode ∈ [0,1])
    (hi : i ∈ carrier g37)
    (hmin : ∀ j ∈ carrier g37, score8 g37 mode i ≤ score8 g37 mode j) :
    realize g37 i = "ɔtʃʊsejbie" := by
  have h := unique_min_observation (selects_G37c mode hm) hi hmin
  exact h.trans (by decide)
#print axioms full_G37c
#print axioms fiber_G37c
#print axioms selects_G37c
#print axioms observed_G37c
end Retained
