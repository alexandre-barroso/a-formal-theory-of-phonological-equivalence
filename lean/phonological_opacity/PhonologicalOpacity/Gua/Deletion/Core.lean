import PhonologicalOpacity.Gua.Core
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def or38 : Input := ⟨["a","tʃ","ɔ","s","ɪ","i","k","u"],[0,0,0,1,1,2,2,2],[2,4,5],[0,0,0]⟩
def c21 : Input := ⟨["w","ʊ","s","ʊ","ɪ","s","ɛ"],[0,0,0,0,1,1,1],[3,4],[0,0]⟩
def c23 : Input := ⟨["w","ʊ","s","ʊ","ɛ","b","ɪ"],[0,0,0,0,1,1,1],[3,4],[0,0]⟩
def policyPair (policy k : Nat) (r : List Nat) : Nat × Nat :=
  if k = 7 ∧ policy = 1 then (0,0)
  else if k = 7 ∧ policy = 2 then (r[4]!,r[5]!) else (r[2]!,r[3]!)
def coefficients (u : Input) (policy i : Nat) : List (Nat × Nat) :=
  (counts u i).zipIdx.map fun (r,k) => policyPair policy k r
def score (u : Input) (policy i : Nat) : Nat :=
  (((coefficients u policy i).zip weights).map fun (r,w) => w*(8*r.1+r.2)).sum
theorem score_V_binding (u : Input) (i : Nat) : score u 0 i = score8 u 1 i := by
  rfl
noncomputable def realPressure (u : Input) (policy : Nat) (w : Fin 9 → ℝ) (lam : ℝ) (i : Nat) : ℝ :=
  ∑ k : Fin 9, w k * ((((coefficients u policy i)[k.val]!).1 : ℝ) +
    lam * (((coefficients u policy i)[k.val]!).2 : ℝ))
def checkRow (u : Input) (policy : Nat) (goals : List Nat) (e i : Nat) : Bool :=
  if i ∈ goals then score u policy i == e else e < score u policy i
def checkAll (u : Input) (policy : Nat) (goals : List Nat) (e : Nat) : Bool :=
  (carrier u).all (checkRow u policy goals e)
def checkBlock (u : Input) (policy : Nat) (goals : List Nat) (e b : Nat) : Bool :=
  (List.range 169).all fun j => checkRow u policy goals e (169*b+j)
theorem assembleBlocks {u : Input} {policy e n : Nat} {goals : List Nat}
    (hn : 13^u.focal.length = 169*n)
    (h : ∀ b < n, checkBlock u policy goals e b = true) : checkAll u policy goals e = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 169*n := by simpa [carrier,hn] using hi
  have hb : i/169 < n := by omega
  have hj : i%169 < 169 := Nat.mod_lt i (by decide)
  have hx := List.all_eq_true.mp (h (i/169) hb) (i%169) (List.mem_range.mpr hj)
  have he : 169*(i/169)+i%169=i := by omega
  simpa only [he] using hx
theorem certificate_minima {u : Input} {policy e : Nat} {goals : List Nat}
    (hc : checkAll u policy goals e = true) (hn : goals ≠ [])
    (hv : goals.all (fun i => (carrier u).contains i) = true)
    (i : Nat) (hi : i ∈ carrier u) :
    (∀ j ∈ carrier u, score u policy i ≤ score u policy j) ↔ i ∈ goals := by
  cases goals with
  | nil => exact False.elim (hn rfl)
  | cons g gs =>
    have hgc : g ∈ carrier u := by simpa using List.all_eq_true.mp hv g (by simp)
    have hx (j : Nat) (hj : j ∈ carrier u) := List.all_eq_true.mp hc j hj
    have hg : score u policy g = e := by simpa [checkRow] using hx g hgc
    constructor
    · intro hm
      by_contra he
      have hh : e < score u policy i := by simpa [checkRow,he] using hx i hi
      have := hm g hgc
      omega
    · intro he j hj
      have heq : score u policy i = e := by simpa [checkRow,he] using hx i hi
      by_cases hjg : j ∈ g::gs
      · have hje : score u policy j = e := by simpa [checkRow,hjg] using hx j hj
        omega
      · have hjt : e < score u policy j := by simpa [checkRow,hjg] using hx j hj
        omega
def Exclusive (u : Input) (P : Nat → ℝ) (out : String) : Prop :=
  (∃ i ∈ carrier u, ∀ j ∈ carrier u, P i ≤ P j) ∧
  ∀ i ∈ carrier u, (∀ j ∈ carrier u, P i ≤ P j) → realize u i = out
theorem exclusive_strict {u : Input} {P : Nat → ℝ} {out : String} {g r : Nat}
    (he : Exclusive u P out) (hf : fiber u out = [g])
    (hr : r ∈ carrier u) (hwrong : realize u r ≠ out) : P g < P r := by
  obtain ⟨⟨i,hi,hm⟩,ho⟩ := he
  have hh : i ∈ fiber u out := by simp [fiber,hi,ho i hi hm]
  rw [hf] at hh
  have hiG : i=g := by simpa using hh
  subst i
  have hle := hm r hr
  by_contra hn
  have hrg : P r ≤ P g := le_of_not_gt hn
  exact hwrong (ho r hr (fun j hj => le_trans hrg (hm j hj)))
#print axioms assembleBlocks
#print axioms score_V_binding
#print axioms certificate_minima
#print axioms exclusive_strict
end Deletion
