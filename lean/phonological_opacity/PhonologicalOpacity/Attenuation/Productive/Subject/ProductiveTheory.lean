import PhonologicalOpacity.Attenuation.Productive.Subject.ProductiveInputs
namespace ProductiveSubjectGua
open Retained
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def enumeration : List (List String) → List (List String)
 | [] => [[]]
 | opts::rest => opts.flatMap fun x => (enumeration rest).map (x::·)

theorem mem_enumeration {rows : List (List String)} {s : List String} :
    s ∈ enumeration rows ↔ Generated rows s := by
  induction rows generalizing s with
  | nil => simp [enumeration,Generated]
  | cons opts rest ih =>
    cases s with
    | nil => simp [enumeration,Generated]
    | cons x xs => simp [enumeration,Generated,ih]

def Exclusive (rows : List (List String)) (P : List String → ℝ) (out : String) : Prop :=
  (∃ s, Generated rows s ∧ ∀ t, Generated rows t → P s ≤ P t) ∧
  ∀ s, Generated rows s → (∀ t, Generated rows t → P s ≤ P t) → observe s=out

theorem exclusive_of_separation {rows : List (List String)} {P : List String → ℝ}
    {out : String} {g : List String} (hg : Generated rows g) (ho : observe g=out)
    (hs : ∀ s, Generated rows s → observe s=out ∨ P g < P s) : Exclusive rows P out := by
  classical
  let candidates := (enumeration rows).toFinset
  have hne : candidates.Nonempty := ⟨g, by simpa [candidates,mem_enumeration] using hg⟩
  obtain ⟨s,hm,hsmin⟩ := Finset.exists_min_image candidates P hne
  have hsg : Generated rows s := by simpa [candidates,mem_enumeration] using hm
  refine ⟨⟨s,hsg,?_⟩,?_⟩
  · intro t ht
    exact hsmin t (by simpa [candidates,mem_enumeration] using ht)
  · intro t ht htmin
    rcases hs t ht with hcorrect | hstrict
    · exact hcorrect
    · exact False.elim (not_lt_of_ge (htmin g hg) hstrict)

theorem observe_append (a b : List String) : observe (a++b) = observe a ++ observe b := by
  simp [observe,List.filter_append,String.join_append]

def fiberCheck (out : String) (goals : List (List String)) (pre : List String) : List (List String) → Bool
 | [] => if observe pre == out then decide (pre ∈ goals) else true
 | opts::rest => if (observe pre).toList <+: out.toList then
      opts.all (fun x => fiberCheck out goals (pre++[x]) rest)
    else true

theorem fiberCheck_sound {rows : List (List String)} {out : String} {goals : List (List String)}
    {pre s : List String} (h : fiberCheck out goals pre rows = true)
    (hs : Generated rows s) (ho : observe (pre++s)=out) : pre++s ∈ goals := by
  induction rows generalizing pre s with
  | nil =>
    have he : s=[] := hs
    subst s
    simp only [List.append_nil] at ho ⊢
    simpa [fiberCheck,ho] using h
  | cons opts rest ih =>
    have hp : (observe pre).toList <+: out.toList := by
      rw [← ho,observe_append,String.toList_append]
      exact List.prefix_append _ _
    have hh : opts.all (fun x => fiberCheck out goals (pre++[x]) rest) = true := by
      simpa [fiberCheck,hp] using h
    cases s with
    | nil => exact False.elim hs
    | cons x xs =>
      have hx : x ∈ opts ∧ Generated rest xs := hs
      have hcheck := List.all_eq_true.mp hh x hx.1
      have hobs : observe ((pre++[x])++xs)=out := by simpa using ho
      simpa using ih hcheck hx.2 hobs

theorem check_of_children {u : Input} {g0 g1 : Int} {out : String} {pre : List String}
    {opts : List String} {rest : List (List String)}
    (h : ∀ x ∈ opts, check u g0 g1 out (pre++[x]) rest = true) :
    check u g0 g1 out pre (opts::rest) = true := by
  simp only [check]
  split
  · rfl
  · exact List.all_eq_true.mpr h

end ProductiveSubjectGua
