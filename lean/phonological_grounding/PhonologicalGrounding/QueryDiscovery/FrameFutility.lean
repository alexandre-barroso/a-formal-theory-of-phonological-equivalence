                  
import Mathlib.Data.Set.Image
import PhonologicalGrounding.Basic

namespace PhonologicalGrounding.QueryDiscovery

structure FramedElicitation (S T A : Type*) where
  frame : S → T
  selectedSource : Set S
  selectedTarget : Set T
  bridge : T → A

namespace FramedElicitation

variable {S T A : Type*} (F : FramedElicitation S T A)

def datum : Set A := F.bridge '' F.selectedTarget

def representational (x : S) : A := F.bridge (F.frame x)

def Commutes : Prop := F.frame '' F.selectedSource = F.selectedTarget

theorem datum_independent_of_source_selection
    (frame : S → T) (sel₁ sel₂ : Set S) (selT : Set T) (bridge : T → A) :
    (FramedElicitation.mk frame sel₁ selT bridge).datum =
      (FramedElicitation.mk frame sel₂ selT bridge).datum := rfl

theorem representational_mem_datum_of_commutes (h : F.Commutes) {x : S}
    (hx : x ∈ F.selectedSource) : F.representational x ∈ F.datum := by
  refine ⟨F.frame x, ?_, rfl⟩
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem datum_eq_image_of_commutes (h : F.Commutes) :
    F.datum = F.representational '' F.selectedSource := by
  unfold datum representational Commutes at *
  rw [← h, Set.image_image]

theorem not_commutes_of_readout_mismatch
    (hne : F.representational '' F.selectedSource ≠ F.datum) : ¬ F.Commutes :=
  fun h => hne (F.datum_eq_image_of_commutes h).symm

theorem datum_singleton_of_commutes_of_unique (h : F.Commutes) {x : S}
    (hx : F.selectedSource = {x}) : F.datum = {F.representational x} := by
  rw [F.datum_eq_image_of_commutes h, hx, Set.image_singleton]

end FramedElicitation

namespace FrameWitness

def good : FramedElicitation Bool Bool Bool where
  frame := id
  selectedSource := {true}
  selectedTarget := {true}
  bridge := id

theorem good_commutes : good.Commutes := by
  simp [FramedElicitation.Commutes, good]

theorem good_reports : good.datum = {true} := by
  have h := good.datum_singleton_of_commutes_of_unique good_commutes (x := true) rfl
  simpa [FramedElicitation.representational, good] using h

def bad : FramedElicitation Bool Bool Bool where
  frame := id
  selectedSource := {true}
  selectedTarget := {false}
  bridge := id

theorem bad_does_not_commute : ¬ bad.Commutes := by
  refine bad.not_commutes_of_readout_mismatch ?_
  simp [FramedElicitation.representational, FramedElicitation.datum, bad]

theorem bad_datum_blind :
    (FramedElicitation.mk (id : Bool → Bool) {true} {false} id).datum =
      (FramedElicitation.mk (id : Bool → Bool) {false} {false} id).datum :=
  FramedElicitation.datum_independent_of_source_selection _ _ _ _ _

end FrameWitness

end PhonologicalGrounding.QueryDiscovery
