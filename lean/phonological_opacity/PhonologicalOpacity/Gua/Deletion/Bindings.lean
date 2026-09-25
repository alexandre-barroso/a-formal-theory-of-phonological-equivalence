import PhonologicalOpacity.Gua.Deletion.Core
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def unitPair (k : Nat) : List (Nat × Nat) :=
  (List.range 9).map fun j => if j=k then (1,0) else (0,0)
def alternateDeletion : List (Nat × Nat) := [(1,0),(0,0),(1,0),(0,0),(0,0),(0,0),(0,0),(0,0),(1,0)]
theorem fibers : fiber or38 "atʃɔsiku" = [1189,1261] ∧
    fiber c21 "wʊsʊsɛ" = [9,117] ∧ fiber c23 "wʊswɛbɪ" = [159] := by decide +kernel
theorem starts : expand or38 1254 = or38.origin ∧ expand c21 122 = c21.origin ∧
    expand c23 120 = c23.origin := by decide
theorem controls_bind : ([1,2].all fun pol =>
    coefficients c23 pol 159 == unitPair 3 && coefficients c23 pol 3 == unitPair 0 &&
    coefficients c21 pol 161 == unitPair 3 && coefficients c21 pol 117 == unitPair 0 &&
    coefficients c21 pol 9 == alternateDeletion) = true := by decide
theorem controls_observe : 3 ∈ carrier c23 ∧ realize c23 3 ≠ "wʊswɛbɪ" ∧
    161 ∈ carrier c21 ∧ realize c21 161 ≠ "wʊsʊsɛ" := by decide
theorem hypotheses_OR38 : score or38 0 1261 = 172 ∧ score or38 0 1267 = 204 ∧
    score or38 1 1267 = 12 ∧ score or38 0 1189 = 356 := by decide
def probeInput : Input := ⟨["e","o","e","e"],[0,1,2,3],[0,1,2,3],[0,0,1,1]⟩
def probeS : List String := ["e","∅","e","e"]
def probeT : List String := ["e","∅","o","e"]
def retainedLocus8 (u : Input) (s : List String) (k q : Nat) : Nat :=
  let r := read u s k q
  let r0 := read u u.origin k q
  let v := r0.context && r0.defined && !r0.good
  let p := r.defined && !r.good
  weights[k]! * (8*(if v && p then 1 else 0) + (if !v && p && r.context then 1 else 0))
theorem probe_binding :
    read probeInput probeInput.origin 5 0 = ⟨true,true,false⟩ ∧
    read probeInput probeS 5 0 = ⟨false,true,true⟩ ∧
    read probeInput probeT 5 0 = ⟨false,true,false⟩ ∧
    nextLive probeInput probeS 0 = some 2 ∧ nextLive probeInput probeT 0 = some 2 ∧
    retainedLocus8 probeInput probeS 5 0 = 0 ∧ retainedLocus8 probeInput probeT 5 0 = 64 ∧
    probeS.take 2 = probeT.take 2 := by decide
theorem no_phrase_local_A : ¬ ∃ f : List String → Nat,
    retainedLocus8 probeInput probeS 5 0 = f (probeS.take 2) ∧
    retainedLocus8 probeInput probeT 5 0 = f (probeT.take 2) := by
  rintro ⟨f,hs,ht⟩
  have h0 : retainedLocus8 probeInput probeS 5 0 = 0 := by decide
  have h1 : retainedLocus8 probeInput probeT 5 0 = 64 := by decide
  have he : probeS.take 2 = probeT.take 2 := by decide
  rw [h0,he] at hs
  rw [h1] at ht
  omega
#print axioms fibers
#print axioms starts
#print axioms controls_bind
#print axioms controls_observe
#print axioms hypotheses_OR38
#print axioms probe_binding
#print axioms no_phrase_local_A
end Deletion
