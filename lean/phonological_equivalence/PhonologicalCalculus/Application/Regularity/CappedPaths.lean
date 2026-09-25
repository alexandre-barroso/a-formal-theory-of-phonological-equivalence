                     
                   
import PhonologicalCalculus.Application.Regularity.BoundedMemory

namespace CappedPaths
open BoundedMemory
variable {Q A I : Type} (M : Machine Q A I)

def expand (P : Set (List A)) (i : I) : Set (List A) :=
  {ys | ∃ xs ∈ P, ∃ a, M.allowed a ∧ M.input a = i ∧ ys = xs ++ [a]}

noncomputable def minimum (P : Set (List A)) : ℕ := sInf (M.cost M.start '' P)
def cap (K : ℕ) (P : Set (List A)) : Set (List A) :=
  {xs ∈ P | M.cost M.start xs ≤ minimum M P + K}
noncomputable def kept (K : ℕ) (us : List I) : Set (List A) :=
  us.foldl (fun P i => cap M K (expand M P i)) {[]}

theorem kept_nil (K : ℕ) : kept M K [] = {[]} := rfl

theorem kept_append (K : ℕ) (us : List I) (i : I) :
    kept M K (us ++ [i]) = cap M K (expand M (kept M K us) i) := by
  simp [kept,List.foldl_append]

theorem kept_valid (K : ℕ) (us : List I) :
    ∀ xs ∈ kept M K us, M.valid xs ∧ xs.map M.input = us := by
  induction us using List.reverseRecOn with
  | nil => simp [kept,Machine.valid]
  | append_singleton us i ih =>
    intro ys hy
    rw [kept_append] at hy
    rcases hy.1 with ⟨xs,hxs,a,ha,hi,rfl⟩
    have hx := ih xs hxs
    refine ⟨(M.valid_append _ _).mpr ⟨hx.1,?_⟩,by simp [hx.2,hi]⟩
    simpa [Machine.valid] using ha

theorem expanded_valid (K : ℕ) (us : List I) (i : I) :
    ∀ xs ∈ expand M (kept M K us) i, M.valid xs ∧ xs.map M.input = us ++ [i] := by
  rintro ys ⟨xs,hxs,a,ha,hi,rfl⟩
  have hx := kept_valid M K us xs hxs
  refine ⟨(M.valid_append _ _).mpr ⟨hx.1,?_⟩,by simp [hx.2,hi]⟩
  simpa [Machine.valid] using ha

theorem minimum_ge_base {P : Set (List A)} {xs : List A} (hn : P.Nonempty)
    (hP : ∀ ys ∈ P, M.valid ys ∧ M.same ys xs) : M.base xs ≤ minimum M P := by
  have hn' : (M.cost M.start '' P).Nonempty := hn.image _
  obtain ⟨ys,hy,he⟩ := Nat.sInf_mem hn'
  rw [minimum,← he]
  exact M.base_le (hP ys hy).1 (hP ys hy).2

theorem optimal_prefix_survives (K : ℕ) (hb : M.bounded K) (xs : List A) :
    ∀ zs, M.winner (xs ++ zs) → xs ∈ kept M K (xs.map M.input) := by
  induction xs using List.reverseRecOn with
  | nil => intros; simp [kept]
  | append_singleton xs a ih =>
    intro zs hw
    have hw' : M.winner (xs ++ (a :: zs)) := by simpa [List.append_assoc] using hw
    have hprev := ih (a :: zs) hw'
    have hva : M.allowed a := hw.1 a (by simp)
    have he : xs ++ [a] ∈ expand M (kept M K (xs.map M.input)) (M.input a) :=
      ⟨xs,hprev,a,hva,rfl,rfl⟩
    have hm := minimum_ge_base M (xs := xs ++ [a]) ⟨xs ++ [a],he⟩ (fun ys hy => by
      have h := expanded_valid M K (xs.map M.input) (M.input a) ys hy
      exact ⟨h.1,by simpa [Machine.same] using h.2⟩)
    have hp := M.optimal_prefix_bound K hb hw
    simp only [List.map_append,List.map_singleton,kept_append]
    exact ⟨he,by omega⟩

theorem optimal_survives (K : ℕ) (hb : M.bounded K) {xs : List A} (h : M.winner xs) :
    xs ∈ kept M K (xs.map M.input) := by
  apply optimal_prefix_survives M K hb xs []
  simpa using h

theorem same_state_cost (xs ys zs : List A)
    (hs : M.state M.start xs = M.state M.start ys)
    (hc : M.cost M.start xs = M.cost M.start ys) :
    M.total M.start (xs ++ zs) = M.total M.start (ys ++ zs) := by
  rw [M.total_append,M.total_append,hs,hc]

theorem lower_state_dominates (xs ys zs : List A)
    (hs : M.state M.start xs = M.state M.start ys)
    (hc : M.cost M.start xs < M.cost M.start ys) :
    M.total M.start (xs ++ zs) < M.total M.start (ys ++ zs) := by
  rw [M.total_append,M.total_append,hs]
  omega

end CappedPaths
