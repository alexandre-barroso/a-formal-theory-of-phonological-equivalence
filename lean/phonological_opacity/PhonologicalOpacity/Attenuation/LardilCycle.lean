import PhonologicalOpacity.Attenuation.Lardil
import Mathlib.Logic.Relation
namespace LardilCycle
open LardilRegion
def PotentialEdge (r q : Bool) : Prop := r ≠ q ∧ ∃ s : State, ∃ i j : Nat,
  (reader s i r (false,false)).1 = true ∧
  (reader s j q (false,false)).1 = false ∧
  (reader (s.set i none) j q (false,false)).1 = true
def Acyclic : Prop := ∀ r, ¬ Relation.TransGen PotentialEdge r r
theorem apocope_creates_c_deletion : PotentialEdge true false := by
  refine ⟨by decide,initial nga.1,7,6,?_⟩
  decide +kernel
theorem c_deletion_creates_apocope : PotentialEdge false true := by
  refine ⟨by decide,candidate nga 1,6,5,?_⟩
  decide +kernel
theorem source_fragment_not_acyclic : ¬ Acyclic := by
  intro h
  exact h true ((Relation.TransGen.single apocope_creates_c_deletion).tail c_deletion_creates_apocope)
theorem no_strict_dependency_rank :
    ¬ ∃ rank : Bool → Nat, ∀ r q, PotentialEdge r q → rank r < rank q := by
  rintro ⟨rank,h⟩
  exact Nat.lt_asymm (h true false apocope_creates_c_deletion) (h false true c_deletion_creates_apocope)
end LardilCycle
