import PhonologicalOpacity.Attenuation.FreeWeights.Bounds
import PhonologicalOpacity.Attenuation.FreeWeights.Selection
import PhonologicalOpacity.Gua.Deletion.Bindings
import PhonologicalOpacity.Gua.Select.G34a
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a00
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a01
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a02
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a03
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a04
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a05
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a06
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a07
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a08
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a09
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a10
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a11
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34a12
import PhonologicalOpacity.Gua.Select.G34b
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b00
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b01
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b02
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b03
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b04
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b05
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b06
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b07
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b08
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b09
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b10
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b11
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G34b12
import PhonologicalOpacity.Gua.Select.N7
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.N700
import PhonologicalOpacity.Gua.Select.G37c
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c00
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c01
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c02
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c03
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c04
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c05
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c06
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c07
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c08
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c09
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c10
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c11
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.G37c12
import PhonologicalOpacity.Gua.Select.C24ei
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.C24ei00
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3800
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3801
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3802
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3803
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3804
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3805
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3806
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3807
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3808
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3809
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3810
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3811
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.OR3812
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.C21b00
import PhonologicalOpacity.Attenuation.FreeWeights.Blocks.C23UE00
                             
namespace FreeWeights
open Retained Deletion
set_option maxRecDepth 100000
theorem polynomial_G34a : polynomial g34a 774 = ⟨3,-2,0⟩ := by decide +kernel
theorem certificate_G34a : checkAll g34a ⟨3,-2,0⟩ [774] = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_G34a00
  · exact block_G34a01
  · exact block_G34a02
  · exact block_G34a03
  · exact block_G34a04
  · exact block_G34a05
  · exact block_G34a06
  · exact block_G34a07
  · exact block_G34a08
  · exact block_G34a09
  · exact block_G34a10
  · exact block_G34a11
  · exact block_G34a12
theorem selects_G34a (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive g34a (pressure g34a (witness l) l) "ahetɔɔkpʊkɔ" :=
  certificate_exclusive certificate_G34a polynomial_G34a (by decide) Retained.fiber_G34a l h0 h1
theorem polynomial_G34b : polynomial g34b 957 = ⟨2,0,0⟩ := by decide +kernel
theorem certificate_G34b : checkAll g34b ⟨2,0,0⟩ [957] = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_G34b00
  · exact block_G34b01
  · exact block_G34b02
  · exact block_G34b03
  · exact block_G34b04
  · exact block_G34b05
  · exact block_G34b06
  · exact block_G34b07
  · exact block_G34b08
  · exact block_G34b09
  · exact block_G34b10
  · exact block_G34b11
  · exact block_G34b12
theorem selects_G34b (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive g34b (pressure g34b (witness l) l) "afɪsoohili" :=
  certificate_exclusive certificate_G34b polynomial_G34b (by decide) Retained.fiber_G34b l h0 h1
theorem polynomial_N7 : polynomial n7 82 = ⟨1,0,0⟩ := by decide +kernel
theorem certificate_N7 : checkAll n7 ⟨1,0,0⟩ [82] = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_N700
theorem selects_N7 (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive n7 (pressure n7 (witness l) l) "atʃijeli" :=
  certificate_exclusive certificate_N7 polynomial_N7 (by decide) Retained.fiber_N7 l h0 h1
theorem polynomial_G37c : polynomial g37 1584 = ⟨3,0,0⟩ := by decide +kernel
theorem certificate_G37c : checkAll g37 ⟨3,0,0⟩ [1584] = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_G37c00
  · exact block_G37c01
  · exact block_G37c02
  · exact block_G37c03
  · exact block_G37c04
  · exact block_G37c05
  · exact block_G37c06
  · exact block_G37c07
  · exact block_G37c08
  · exact block_G37c09
  · exact block_G37c10
  · exact block_G37c11
  · exact block_G37c12
theorem selects_G37c (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive g37 (pressure g37 (witness l) l) "ɔtʃʊsejbie" :=
  certificate_exclusive certificate_G37c polynomial_G37c (by decide) Retained.fiber_G37c l h0 h1
theorem polynomial_C24ei : polynomial c24 63 = ⟨2,-2,0⟩ := by decide +kernel
theorem certificate_C24ei : checkAll c24 ⟨2,-2,0⟩ [63] = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C24ei00
theorem selects_C24ei (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive c24 (pressure c24 (witness l) l) "kpejsi" :=
  certificate_exclusive certificate_C24ei polynomial_C24ei (by decide) Retained.fiber_C24ei l h0 h1
theorem polynomial_OR38 : polynomial or38 1261 = ⟨4,-2,0⟩ := by decide +kernel
theorem certificate_OR38 : checkAll or38 ⟨4,-2,0⟩ [1189,1261] = true := by
  apply assemble (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact block_OR3800
  · exact block_OR3801
  · exact block_OR3802
  · exact block_OR3803
  · exact block_OR3804
  · exact block_OR3805
  · exact block_OR3806
  · exact block_OR3807
  · exact block_OR3808
  · exact block_OR3809
  · exact block_OR3810
  · exact block_OR3811
  · exact block_OR3812
theorem selects_OR38 (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive or38 (pressure or38 (witness l) l) "atʃɔsiku" :=
  certificate_exclusive certificate_OR38 polynomial_OR38 (by decide) Deletion.fibers.1 l h0 h1
theorem polynomial_C21b : polynomial c21 117 = ⟨3,-4,0⟩ := by decide +kernel
theorem certificate_C21b : checkAll c21 ⟨3,-4,0⟩ [9,117] = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C21b00
theorem selects_C21b (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive c21 (pressure c21 (witness l) l) "wʊsʊsɛ" :=
  certificate_exclusive certificate_C21b polynomial_C21b (by decide) Deletion.fibers.2.1 l h0 h1
theorem polynomial_C23UE : polynomial c23 159 = ⟨2,-2,0⟩ := by decide +kernel
theorem certificate_C23UE : checkAll c23 ⟨2,-2,0⟩ [159] = true := by
  apply assemble (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact block_C23UE00
theorem selects_C23UE (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive c23 (pressure c23 (witness l) l) "wʊswɛbɪ" :=
  certificate_exclusive certificate_C23UE polynomial_C23UE (by decide) Deletion.fibers.2.2 l h0 h1
def Joint (w : Fin 9 → ℝ) (l : ℝ) : Prop :=
  Exclusive g34a (pressure g34a w l) "ahetɔɔkpʊkɔ" ∧
  Exclusive g34b (pressure g34b w l) "afɪsoohili" ∧
  Exclusive n7 (pressure n7 w l) "atʃijeli" ∧
  Exclusive g37 (pressure g37 w l) "ɔtʃʊsejbie" ∧
  Exclusive c24 (pressure c24 w l) "kpejsi" ∧
  Exclusive or38 (pressure or38 w l) "atʃɔsiku" ∧
  Exclusive c21 (pressure c21 w l) "wʊsʊsɛ" ∧
  Exclusive c23 (pressure c23 w l) "wʊswɛbɪ"
theorem joint_witness (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) : Joint (witness l) l :=
  ⟨selects_G34a l h0 h1, selects_G34b l h0 h1, selects_N7 l h0 h1, selects_G37c l h0 h1, selects_C24ei l h0 h1, selects_OR38 l h0 h1, selects_C21b l h0 h1, selects_C23UE l h0 h1⟩
theorem exact_region (l : ℝ) (h0 : 0 ≤ l) :
    (∃ w : Fin 9 → ℝ, (∀ k, 0 ≤ w k) ∧ Joint w l) ↔ l < 1/2 := by
  constructor
  · rintro ⟨w, hw, hj⟩
    exact necessary_bound w l (hw 4) hj.2.1 hj.2.2.2.1
  · intro h1
    exact ⟨witness l, witness_nonnegative l h0 h1, joint_witness l h0 h1⟩
theorem downward_closed (l t : ℝ) (ht : 0 ≤ t) (htl : t ≤ l)
    (h : ∃ w : Fin 9 → ℝ, (∀ k, 0 ≤ w k) ∧ Joint w l) :
    ∃ w : Fin 9 → ℝ, (∀ k, 0 ≤ w k) ∧ Joint w t := by
  apply (exact_region t ht).2
  exact lt_of_le_of_lt htl ((exact_region l (le_trans ht htl)).1 h)
end FreeWeights
