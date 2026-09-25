import PhonologicalOpacity.Attenuation.FreeWeights.Core
namespace FreeWeights
open Retained Deletion

theorem exclusive_of_separation (u : Input) (P : Nat → ℝ) (out : String)
    (goal : Nat) (hg : goal ∈ carrier u)
    (hs : ∀ i ∈ carrier u, realize u i ≠ out → P goal < P i) : Exclusive u P out := by
  have hn : (carrier u).toFinset.Nonempty := ⟨goal, by simpa using hg⟩
  obtain ⟨i, hi, hm⟩ := (carrier u).toFinset.exists_min_image P hn
  have hi' : i ∈ carrier u := by simpa using hi
  have hm' : ∀ j ∈ carrier u, P i ≤ P j := by
    intro j hj
    exact hm j (by simpa using hj)
  refine ⟨⟨i, hi', hm'⟩, ?_⟩
  intro k hk hmin
  by_contra hwrong
  exact (not_lt_of_ge (hmin goal hg)) (hs k hk hwrong)

theorem certificate_exclusive {u : Input} {g : Polynomial} {correct : List Nat}
    {goal : Nat} {out : String} (hc : checkAll u g correct = true)
    (hp : polynomial u goal = g) (hg : goal ∈ carrier u)
    (hf : fiber u out = correct) (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    Exclusive u (pressure u (witness l) l) out := by
  apply exclusive_of_separation u _ out goal hg
  intro i hi hwrong
  have hnot : i ∉ correct := by
    intro hc
    rw [← hf] at hc
    have hh : realize u i = out := by simpa [fiber] using (List.mem_filter.mp hc).2
    exact hwrong hh
  exact strict_separation hc hp l h0 h1 i hi hnot
end FreeWeights
