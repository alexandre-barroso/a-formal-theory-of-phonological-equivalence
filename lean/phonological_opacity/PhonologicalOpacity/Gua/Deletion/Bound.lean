import PhonologicalOpacity.Gua.Deletion.Bindings
namespace Deletion
open Retained
theorem control_pressures (pol : Nat) (hp : pol ∈ [1,2]) (w : Fin 9 → ℝ) (lam : ℝ) :
    realPressure c23 pol w lam 159 = w 3 ∧ realPressure c23 pol w lam 3 = w 0 ∧
    realPressure c21 pol w lam 161 = w 3 ∧ realPressure c21 pol w lam 117 = w 0 ∧
    realPressure c21 pol w lam 9 = w 0+w 2+w 8 := by
  have h := List.all_eq_true.mp controls_bind pol hp
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  obtain ⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩ := h
  simp [realPressure,a,b,c,d,e,unitPair,alternateDeletion,Fin.sum_univ_succ]
  <;> ring
theorem no_joint_exclusive (pol : Nat) (hp : pol ∈ [1,2]) (w : Fin 9 → ℝ) (lam : ℝ)
    (hw : ∀ k, 0 ≤ w k) :
    ¬ (Exclusive c23 (realPressure c23 pol w lam) "wʊswɛbɪ" ∧
       Exclusive c21 (realPressure c21 pol w lam) "wʊsʊsɛ") := by
  rintro ⟨h23,h21⟩
  obtain ⟨hG,hR,hGl,hD,hAlt⟩ := control_pressures pol hp w lam
  have lt := exclusive_strict h23 fibers.2.2 controls_observe.1 controls_observe.2.1
  rw [hG,hR] at lt
  obtain ⟨⟨i,hi,hm⟩,ho⟩ := h21
  have hf : i ∈ fiber c21 "wʊsʊsɛ" := by simp [fiber,hi,ho i hi hm]
  rw [fibers.2.1] at hf
  have htwo : i=9 ∨ i=117 := by simpa using hf
  have hmin := hm 161 controls_observe.2.2.1
  rcases htwo with h | h
  · subst i
    rw [hAlt,hGl] at hmin
    linarith [hw 2,hw 8]
  · subst i
    rw [hD,hGl] at hmin
    linarith
#print axioms control_pressures
#print axioms no_joint_exclusive
end Deletion
