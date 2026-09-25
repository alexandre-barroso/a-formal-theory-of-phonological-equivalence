import PhonologicalOpacity.Attenuation.FreeWeights.Complete
import PhonologicalOpacity.Attenuation.FreeWeights.Subject
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a00
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a01
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a02
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a03
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a04
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a05
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a06
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a07
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a08
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a09
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a10
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a11
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34a12
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b00
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b01
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b02
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b03
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b04
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b05
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b06
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b07
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b08
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b09
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b10
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b11
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G34b12
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.N700
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c00
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c01
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c02
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c03
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c04
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c05
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c06
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c07
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c08
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c09
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c10
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c11
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.G37c12
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.C24ei00
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3800
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3801
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3802
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3803
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3804
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3805
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3806
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3807
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3808
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3809
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3810
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3811
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.OR3812
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.C21b00
import PhonologicalOpacity.Attenuation.FreeWeights.Transfers.C23UE00
                             
namespace FreeWeights
open Retained Deletion
set_option maxRecDepth 100000
theorem unchanged_G34a : subjectPair g34a 774 = (coefficients g34a 0 774)[5]! := by decide +kernel
theorem transfer_certificate_G34a : checkTransferAll g34a ⟨3,-2,0⟩ [774] = true := by
  apply assembleTransfer (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_G34a00
  · exact transfer_G34a01
  · exact transfer_G34a02
  · exact transfer_G34a03
  · exact transfer_G34a04
  · exact transfer_G34a05
  · exact transfer_G34a06
  · exact transfer_G34a07
  · exact transfer_G34a08
  · exact transfer_G34a09
  · exact transfer_G34a10
  · exact transfer_G34a11
  · exact transfer_G34a12
theorem subject_selects_G34a (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive g34a (subjectPressure g34a (witness l) l) "ahetɔɔkpʊkɔ" :=
  subject_certificate_exclusive certificate_G34a transfer_certificate_G34a
    polynomial_G34a unchanged_G34a (by decide) Retained.fiber_G34a l h0 h1
theorem unchanged_G34b : subjectPair g34b 957 = (coefficients g34b 0 957)[5]! := by decide +kernel
theorem transfer_certificate_G34b : checkTransferAll g34b ⟨2,0,0⟩ [957] = true := by
  apply assembleTransfer (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_G34b00
  · exact transfer_G34b01
  · exact transfer_G34b02
  · exact transfer_G34b03
  · exact transfer_G34b04
  · exact transfer_G34b05
  · exact transfer_G34b06
  · exact transfer_G34b07
  · exact transfer_G34b08
  · exact transfer_G34b09
  · exact transfer_G34b10
  · exact transfer_G34b11
  · exact transfer_G34b12
theorem subject_selects_G34b (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive g34b (subjectPressure g34b (witness l) l) "afɪsoohili" :=
  subject_certificate_exclusive certificate_G34b transfer_certificate_G34b
    polynomial_G34b unchanged_G34b (by decide) Retained.fiber_G34b l h0 h1
theorem unchanged_N7 : subjectPair n7 82 = (coefficients n7 0 82)[5]! := by decide +kernel
theorem transfer_certificate_N7 : checkTransferAll n7 ⟨1,0,0⟩ [82] = true := by
  apply assembleTransfer (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_N700
theorem subject_selects_N7 (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive n7 (subjectPressure n7 (witness l) l) "atʃijeli" :=
  subject_certificate_exclusive certificate_N7 transfer_certificate_N7
    polynomial_N7 unchanged_N7 (by decide) Retained.fiber_N7 l h0 h1
theorem unchanged_G37c : subjectPair g37 1584 = (coefficients g37 0 1584)[5]! := by decide +kernel
theorem transfer_certificate_G37c : checkTransferAll g37 ⟨3,0,0⟩ [1584] = true := by
  apply assembleTransfer (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_G37c00
  · exact transfer_G37c01
  · exact transfer_G37c02
  · exact transfer_G37c03
  · exact transfer_G37c04
  · exact transfer_G37c05
  · exact transfer_G37c06
  · exact transfer_G37c07
  · exact transfer_G37c08
  · exact transfer_G37c09
  · exact transfer_G37c10
  · exact transfer_G37c11
  · exact transfer_G37c12
theorem subject_selects_G37c (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive g37 (subjectPressure g37 (witness l) l) "ɔtʃʊsejbie" :=
  subject_certificate_exclusive certificate_G37c transfer_certificate_G37c
    polynomial_G37c unchanged_G37c (by decide) Retained.fiber_G37c l h0 h1
theorem unchanged_C24ei : subjectPair c24 63 = (coefficients c24 0 63)[5]! := by decide +kernel
theorem transfer_certificate_C24ei : checkTransferAll c24 ⟨2,-2,0⟩ [63] = true := by
  apply assembleTransfer (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_C24ei00
theorem subject_selects_C24ei (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive c24 (subjectPressure c24 (witness l) l) "kpejsi" :=
  subject_certificate_exclusive certificate_C24ei transfer_certificate_C24ei
    polynomial_C24ei unchanged_C24ei (by decide) Retained.fiber_C24ei l h0 h1
theorem unchanged_OR38 : subjectPair or38 1261 = (coefficients or38 0 1261)[5]! := by decide +kernel
theorem transfer_certificate_OR38 : checkTransferAll or38 ⟨4,-2,0⟩ [1189,1261] = true := by
  apply assembleTransfer (n := 13) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_OR3800
  · exact transfer_OR3801
  · exact transfer_OR3802
  · exact transfer_OR3803
  · exact transfer_OR3804
  · exact transfer_OR3805
  · exact transfer_OR3806
  · exact transfer_OR3807
  · exact transfer_OR3808
  · exact transfer_OR3809
  · exact transfer_OR3810
  · exact transfer_OR3811
  · exact transfer_OR3812
theorem subject_selects_OR38 (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive or38 (subjectPressure or38 (witness l) l) "atʃɔsiku" :=
  subject_certificate_exclusive certificate_OR38 transfer_certificate_OR38
    polynomial_OR38 unchanged_OR38 (by decide) Deletion.fibers.1 l h0 h1
theorem unchanged_C21b : subjectPair c21 117 = (coefficients c21 0 117)[5]! := by decide +kernel
theorem transfer_certificate_C21b : checkTransferAll c21 ⟨3,-4,0⟩ [9,117] = true := by
  apply assembleTransfer (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_C21b00
theorem subject_selects_C21b (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive c21 (subjectPressure c21 (witness l) l) "wʊsʊsɛ" :=
  subject_certificate_exclusive certificate_C21b transfer_certificate_C21b
    polynomial_C21b unchanged_C21b (by decide) Deletion.fibers.2.1 l h0 h1
theorem unchanged_C23UE : subjectPair c23 159 = (coefficients c23 0 159)[5]! := by decide +kernel
theorem transfer_certificate_C23UE : checkTransferAll c23 ⟨2,-2,0⟩ [159] = true := by
  apply assembleTransfer (n := 1) (by decide)
  intro b hb
  interval_cases b
  · exact transfer_C23UE00
theorem subject_selects_C23UE (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive c23 (subjectPressure c23 (witness l) l) "wʊswɛbɪ" :=
  subject_certificate_exclusive certificate_C23UE transfer_certificate_C23UE
    polynomial_C23UE unchanged_C23UE (by decide) Deletion.fibers.2.2 l h0 h1
def SubjectJoint (w : Fin 9 → ℝ) (l : ℝ) : Prop :=
  Exclusive g34a (subjectPressure g34a w l) "ahetɔɔkpʊkɔ" ∧
  Exclusive g34b (subjectPressure g34b w l) "afɪsoohili" ∧
  Exclusive n7 (subjectPressure n7 w l) "atʃijeli" ∧
  Exclusive g37 (subjectPressure g37 w l) "ɔtʃʊsejbie" ∧
  Exclusive c24 (subjectPressure c24 w l) "kpejsi" ∧
  Exclusive or38 (subjectPressure or38 w l) "atʃɔsiku" ∧
  Exclusive c21 (subjectPressure c21 w l) "wʊsʊsɛ" ∧
  Exclusive c23 (subjectPressure c23 w l) "wʊswɛbɪ"
theorem subject_joint_witness (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) : SubjectJoint (witness l) l :=
  ⟨subject_selects_G34a l h0 h1, subject_selects_G34b l h0 h1, subject_selects_N7 l h0 h1, subject_selects_G37c l h0 h1, subject_selects_C24ei l h0 h1, subject_selects_OR38 l h0 h1, subject_selects_C21b l h0 h1, subject_selects_C23UE l h0 h1⟩
theorem subject_necessary_bound (w : Fin 9 → ℝ) (l : ℝ) (hw : 0 ≤ w 4)
    (h34 : Exclusive g34b (subjectPressure g34b w l) "afɪsoohili")
    (h37 : Exclusive g37 (subjectPressure g37 w l) "ɔtʃʊsejbie") : l < 1/2 := by
  have h34' : subjectPressure g34b w l 957 < subjectPressure g34b w l 1126 :=
    exclusive_strict h34 fiber_G34b (by decide) (by decide +kernel)
  have h37' : subjectPressure g37 w l 1584 < subjectPressure g37 w l 1571 :=
    exclusive_strict h37 fiber_G37c (by decide) (by decide +kernel)
  rw [unchanged_pressure g34b 957 w l unchanged_G34b,
    unchanged_pressure g34b 1126 w l (by decide +kernel)] at h34'
  rw [unchanged_pressure g37 1584 w l unchanged_G37c,
    unchanged_pressure g37 1571 w l (by decide +kernel)] at h37'
  have ha := critical_G34b w l
  have hb := critical_G37c w l
  by_contra hn
  have hhalf : 1/2 ≤ l := le_of_not_gt hn
  have hprod : 0 ≤ (2*l-1)*w 4 := mul_nonneg (by linarith) hw
  nlinarith

theorem subject_exact_region (l : ℝ) (h0 : 0 ≤ l) :
    (∃ w : Fin 9 → ℝ, (∀ k, 0 ≤ w k) ∧ SubjectJoint w l) ↔ l < 1/2 := by
  constructor
  · rintro ⟨w, hw, hj⟩
    exact subject_necessary_bound w l (hw 4) hj.2.1 hj.2.2.2.1
  · intro h1
    exact ⟨witness l, witness_nonnegative l h0 h1, subject_joint_witness l h0 h1⟩

theorem equal_attenuation_projections (l : ℝ) (h0 : 0 ≤ l) :
    (∃ w : Fin 9 → ℝ, (∀ k, 0 ≤ w k) ∧ Joint w l) ↔
    (∃ w : Fin 9 → ℝ, (∀ k, 0 ≤ w k) ∧ SubjectJoint w l) := by
  rw [exact_region l h0, subject_exact_region l h0]
end FreeWeights

