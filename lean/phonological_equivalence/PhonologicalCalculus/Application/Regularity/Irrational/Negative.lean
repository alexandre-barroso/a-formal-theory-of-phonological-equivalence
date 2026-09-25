                  
                   
import PhonologicalCalculus.Application.Regularity.Irrational.BinaryMinima

namespace NativeIrrational

theorem separator_ordered (n m : ℕ) (h : residue n < residue m) :
    ∃ k, 0<k ∧ word n ++ suffix k ∈ constantLanguage ∧ word m ++ suffix k ∉ constantLanguage := by
  obtain ⟨k,hk,hlo,hhi⟩ := positive_orbit_dense (1-residue m) (1-residue n)
    (by linarith [(residue_bounds m).2]) (by linarith) (by linarith [(residue_bounds n).1])
  refine ⟨k,hk,?_,?_⟩
  · rw [constant_winner_stable _ (concat_stable n k),balance_append,balance_word,balance_suffix]
    linarith
  · rw [constant_winner_stable _ (concat_stable m k),balance_append,balance_word,balance_suffix]
    linarith

theorem separator (n m : ℕ) (h : n≠m) :
    ∃ k, (word n ++ suffix k ∈ constantLanguage) ≠ (word m ++ suffix k ∈ constantLanguage) := by
  have hr : residue n ≠ residue m := fun h' => h (residue_injective h')
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · obtain ⟨k,_,hn,hm⟩ := separator_ordered n m hlt
    exact ⟨k,fun he => hm (he ▸ hn)⟩
  · obtain ⟨k,_,hm,hn⟩ := separator_ordered m n hgt
    exact ⟨k,fun he => hn (he ▸ hm)⟩

theorem not_regular_distinguishable {α : Type} (L : Language α) (pref : ℕ → List α)
    (sep : ∀ m n, m ≠ n → ∃ tail, (pref m ++ tail ∈ L) ≠ (pref n ++ tail ∈ L)) :
    ¬ L.IsRegular := by
  rintro ⟨Q,inst,M,hM⟩
  have inj : Function.Injective (fun n => M.eval (pref n)) := by
    intro m n h
    by_contra hn
    obtain ⟨tail,ht⟩ := sep m n hn
    apply ht
    rw [← hM]
    apply propext
    simp only [DFA.mem_accepts,DFA.eval,DFA.evalFrom,List.foldl_append]
    change (List.foldl M.step (M.eval (pref m)) tail ∈ M.accept ↔ List.foldl M.step (M.eval (pref n)) tail ∈ M.accept)
    change M.eval (pref m) = M.eval (pref n) at h
    rw [h]
  letI : Finite ℕ := Finite.of_injective _ inj
  exact not_finite ℕ

theorem constant_language_nonregular : ¬ constantLanguage.IsRegular := by
  apply not_regular_distinguishable constantLanguage word
  intro m n h
  obtain ⟨k,hk⟩ := separator m n h
  exact ⟨suffix k,hk⟩

theorem full_winner_relation_nonregular : ¬ winnerLanguage.IsRegular := by
  apply not_regular_distinguishable winnerLanguage (fun n => constant (word n) false)
  intro m n h
  obtain ⟨k,hk⟩ := separator m n h
  refine ⟨constant (suffix k) false,?_⟩
  change (constant (word m ++ suffix k) false ∈ winnerLanguage) ≠ (constant (word n ++ suffix k) false ∈ winnerLanguage) at hk
  simpa only [constant,List.map_append] using hk

theorem minimum_word (n : ℕ) : minimum (word n) = (unaryTotals (word n)).2 := by
  have h := totals_balance (word n)
  rw [balance_word] at h
  have hr := (residue_bounds n).1
  simp only [minimum,dp_stable _ (word_stable n)]
  exact min_eq_right (by linarith)

theorem continuation_formula (n k : ℕ) :
    minimum (word n ++ suffix k) - minimum (word n) =
      min ((unaryTotals (suffix k)).1+residue n) (unaryTotals (suffix k)).2 := by
  have h := totals_balance (word n)
  rw [balance_word] at h
  rw [minimum_word]
  simp only [minimum,dp_stable _ (concat_stable n k),totals_append]
  by_cases he : (unaryTotals (suffix k)).1+residue n ≤ (unaryTotals (suffix k)).2
  · rw [min_eq_left he,min_eq_left (by linarith)]
    linarith
  · rw [min_eq_right (le_of_not_ge he),min_eq_right (by linarith)]
    ring

theorem continuation_separates (n m : ℕ) (hne : n≠m) :
    ∃ z, minimum (word n ++ z)-minimum (word n) ≠ minimum (word m ++ z)-minimum (word m) := by
  have hr : residue n ≠ residue m := fun h' => hne (residue_injective h')
  suffices hh : ∀ i j, residue i < residue j → ∃ z,
      minimum (word i ++ z)-minimum (word i) < minimum (word j ++ z)-minimum (word j) by
    rcases lt_or_gt_of_ne hr with h | h
    · obtain ⟨z,hz⟩ := hh n m h; exact ⟨z,ne_of_lt hz⟩
    · obtain ⟨z,hz⟩ := hh m n h; exact ⟨z,ne_of_gt hz⟩
  intro i j hij
  obtain ⟨k,_,hl,hu⟩ := positive_orbit_dense (1-residue j) (1-residue i)
    (by linarith [(residue_bounds j).2]) (by linarith) (by linarith [(residue_bounds i).1])
  refine ⟨suffix k,?_⟩
  rw [continuation_formula,continuation_formula]
  have ht := totals_balance (suffix k)
  rw [balance_suffix] at ht
  rw [min_eq_left (by linarith),min_eq_right (by linarith)]
  linarith

structure WeightedMachine (Q : Type) where
  initial : Q
  transition : Q → Bool → Q
  weight : Q → Bool → ℝ
  finalWeight : Q → ℝ
  initialWeight : ℝ

def WeightedMachine.state {Q : Type} (M : WeightedMachine Q) (q : Q) (u : List Bool) : Q :=
  u.foldl M.transition q
noncomputable def WeightedMachine.emission {Q : Type} (M : WeightedMachine Q) : Q → List Bool → ℝ
  | _, [] => 0
  | q,x::xs => M.weight q x + M.emission (M.transition q x) xs
noncomputable def WeightedMachine.value {Q : Type} (M : WeightedMachine Q) (u : List Bool) : ℝ :=
  M.initialWeight + M.emission M.initial u + M.finalWeight (M.state M.initial u)

theorem WeightedMachine.emission_append {Q : Type} (M : WeightedMachine Q)
    (q : Q) (u v : List Bool) :
    M.emission q (u++v) = M.emission q u + M.emission (M.state q u) v := by
  induction u generalizing q with
  | nil => simp [emission,state]
  | cons x u ih => simp [emission,state,ih,add_assoc]

theorem WeightedMachine.same_state_residue {Q : Type} (M : WeightedMachine Q)
    (u v z : List Bool) (h : M.state M.initial u = M.state M.initial v) :
    M.value (u++z)-M.value u = M.value (v++z)-M.value v := by
  simp only [value,emission_append,state,List.foldl_append] at *
  rw [h]
  ring

theorem no_finite_weighted_machine {Q : Type} [Finite Q] (M : WeightedMachine Q) :
    ¬ (∀ u, M.value u = minimum u) := by
  intro h
  have inj : Function.Injective (fun n => M.state M.initial (word n)) := by
    intro n m he
    by_contra hn
    obtain ⟨z,hz⟩ := continuation_separates n m hn
    have hg := M.same_state_residue (word n) (word m) z he
    simp only [h] at hg
    exact hz hg
  letI : Finite ℕ := Finite.of_injective _ inj
  exact not_finite ℕ
end NativeIrrational
