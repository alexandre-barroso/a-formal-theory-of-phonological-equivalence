import PhonologicalOpacity.Gua.Select.G34a
import PhonologicalOpacity.Gua.Select.G34b
import PhonologicalOpacity.Gua.Select.N7
import PhonologicalOpacity.Gua.Select.G37c
import PhonologicalOpacity.Gua.Select.C24ei
import PhonologicalOpacity.Gua.Deletion.Core
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def initialD (u : Input) (q : Nat) : Bool :=
  let r := read u u.origin 7 q
  r.context && r.defined && !r.good
def emptyInitialD (u : Input) : Prop := ∀ q ∈ positions u, initialD u q = false
theorem baseline_initialD : [g34a,g34b,n7,g37,c24].all
    (fun u => (positions u).all (fun q => !initialD u q)) = true := by decide
theorem empty_initial_pairs (a p b : Bool) (h : a=false) :
    ((p && a) = (p && b && a)) ∧ ((p && !a && b) = (p && b && !a)) := by
  subst a
  cases p <;> cases b <;> decide
theorem d_count_identity {u : Input} (h : emptyInitialD u) (i : Nat) :
    ((counts u i)[7]!)[2]! = ((counts u i)[7]!)[4]! ∧
    ((counts u i)[7]!)[3]! = ((counts u i)[7]!)[5]! := by
  constructor <;>
    simp [counts,List.map_map,Function.comp_def] <;>
    congr 1 <;> apply List.map_congr_left <;> intro q hq
  all_goals
    have hz := h q hq
    cases hc : (read u u.origin 7 q).context <;>
      cases hd : (read u u.origin 7 q).defined <;>
      cases hg : (read u u.origin 7 q).good <;>
      simp_all [initialD]
theorem score_current_identity {u : Input} (h : emptyInitialD u) (i : Nat) :
    score u 0 i = score u 2 i := by
  obtain ⟨ha,hb⟩ := d_count_identity h i
  have hc : coefficients u 0 i = coefficients u 2 i := by
    unfold coefficients
    apply List.map_congr_left
    rintro ⟨r,k⟩ hk
    dsimp
    by_cases he : k=7
    · subst k
      have hr := List.mk_mem_zipIdx_iff_getElem?.mp hk
      have hr' : (counts u i)[7]! = r := by
        simp [List.getElem!_eq_getElem?_getD,hr]
      change (r[2]!,r[3]!) = (r[4]!,r[5]!)
      rw [←hr']
      exact Prod.ext ha hb
    · simp [policyPair,he]
  unfold score
  rw [hc]
theorem baseline_empty {u : Input} (hu : u ∈ [g34a,g34b,n7,g37,c24]) : emptyInitialD u := by
  have h := List.all_eq_true.mp baseline_initialD u hu
  intro q hq
  have hz := List.all_eq_true.mp h q hq
  simpa using hz
theorem transfer_current_unique {u : Input} {goal : Nat} (h : emptyInitialD u)
    (hv : UniqueMin u (score8 u 1) goal) : UniqueMin u (score u 2) goal := by
  refine ⟨hv.1,?_⟩
  intro i hi hne
  rw [←score_current_identity h goal,score_V_binding,
      ←score_current_identity h i,score_V_binding]
  exact hv.2 i hi hne
theorem five_current_preserved :
    UniqueMin g34a (score g34a 2) 774 ∧ UniqueMin g34b (score g34b 2) 957 ∧
    UniqueMin n7 (score n7 2) 82 ∧ UniqueMin g37 (score g37 2) 1584 ∧
    UniqueMin c24 (score c24 2) 63 := by
  exact ⟨transfer_current_unique (baseline_empty (by simp)) (selects_G34a 1 (by decide)),
    transfer_current_unique (baseline_empty (by simp)) (selects_G34b 1 (by decide)),
    transfer_current_unique (baseline_empty (by simp)) (selects_N7 1 (by decide)),
    transfer_current_unique (baseline_empty (by simp)) (selects_G37c 1 (by decide)),
    transfer_current_unique (baseline_empty (by simp)) (selects_C24ei 1 (by decide))⟩
#print axioms baseline_initialD
#print axioms empty_initial_pairs
#print axioms d_count_identity
#print axioms score_current_identity
#print axioms baseline_empty
#print axioms transfer_current_unique
#print axioms five_current_preserved
end Deletion
