import PhonologicalOpacity.Gua.Reader
namespace Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def g34a : Input := ⟨["a","h","ɛ","t","e","ɔ","k","p","ʊ","k","ɔ"],[0,0,0,1,1,2,2,2,2,2,2],[2,4,5],[0,0,0]⟩
def g34b : Input := ⟨["a","f","ɪ","s","ɛ","o","h","i","l","i"],[0,0,0,1,1,2,2,2,2,2],[2,4,5],[0,0,0]⟩
def c24 : Input := ⟨["k","p","e","i","s","i"],[0,0,0,1,1,1],[2,3],[0,0]⟩
def counts (u : Input) (i : Nat) : List (List Nat) :=
  let s := expand u i
  (List.range 9).map fun k =>
    let loci := (positions u).map fun q =>
      let r := read u s k q
      let r0 := read u u.origin k q
      let p := r.defined && !r.good
      let a := r0.context
      let v := a && r0.defined && !r0.good
      if 4 ≤ k && k ≤ 7 then
        [p && a,p && !a && r.context,p && v,p && !v && r.context,
         p && r.context && v,p && r.context && !v]
      else [p && r.context,false,p && r.context,false,p && r.context,false]
    (List.range 6).map fun j => (loci.map fun xs => if xs[j]! then 1 else 0).sum
def weights : List Nat := [20,1,1,2,4,8,8,24,1]
def score8 (u : Input) (mode i : Nat) : Nat :=
  (((counts u i).zip weights).map fun (r,w) => w*(8*r[2*mode]!+r[2*mode+1]!)).sum
def complete (u : Input) (goal expected : Nat) : Bool :=
  (carrier u).all fun i => [0,1].all fun mode =>
    if i == goal then score8 u mode i == expected else expected < score8 u mode i

def UniqueMin (u : Input) (P : Nat → Nat) (s : Nat) : Prop :=
  s ∈ carrier u ∧ ∀ t ∈ carrier u, t ≠ s → P s < P t
theorem complete_unique {u : Input} {goal expected mode : Nat}
    (hc : complete u goal expected = true) (hg : goal ∈ carrier u)
    (hm : mode ∈ [0,1]) : UniqueMin u (score8 u mode) goal := by
  have h := List.all_eq_true.mp hc
  have hx (i) (hi : i ∈ carrier u) := List.all_eq_true.mp (h i hi) mode hm
  have he : score8 u mode goal = expected := by simpa using hx goal hg
  refine ⟨hg,?_⟩
  intro t ht hne
  have hv : expected < score8 u mode t := by simpa [hne] using hx t ht
  simpa [he] using hv
theorem unique_min_observation {u : Input} {P : Nat → Nat} {goal i : Nat}
    (h : UniqueMin u P goal) (hi : i ∈ carrier u)
    (hm : ∀ j ∈ carrier u, P i ≤ P j) : realize u i = realize u goal := by
  by_cases he : i = goal
  · simp [he]
  · have := h.2 i hi he; have := hm goal h.1; omega

noncomputable def cmPressure (u : Input) (old new : Fin 9 → ℝ) (i : Nat) : ℝ :=
  ∑ k : Fin 9, (old k * (((counts u i)[k.val]!)[4]! : ℝ) +
    new k * (((counts u i)[k.val]!)[5]! : ℝ))
def rz : List Nat := [0,0,0,0,0,0]
def rf : List Nat := [1,0,1,0,1,0]
def rf2 : List Nat := [2,0,2,0,2,0]
def retainedH : List Nat := [1,0,1,0,0,0]
theorem bound_goal_counts : counts g34a 774 = [rz,rf2,rf,rz,rz,rz,rz,rz,rz] := by decide
theorem bound_rival_counts : counts g34a 605 = [rz,rf,rf,rz,retainedH,rz,rz,rz,rz] := by decide
theorem bound_readout : fiber g34a "ahetɔɔkpʊkɔ" = [774] ∧
    realize g34a 605 = "ahɛtɔɔkpʊkɔ" ∧ 605 ∈ carrier g34a := by decide
theorem bound_pressures (old new : Fin 9 → ℝ) :
    cmPressure g34a old new 774 = 2*old 1+old 2 ∧
    cmPressure g34a old new 605 = old 1+old 2 := by
  simp [cmPressure,bound_goal_counts,bound_rival_counts,rz,rf,rf2,retainedH,Fin.sum_univ_succ]
  <;> ring
theorem global_bound (old new : Fin 9 → ℝ) (hw : 0 ≤ old 1) :
    cmPressure g34a old new 605 ≤ cmPressure g34a old new 774 := by
  obtain ⟨a,b⟩ := bound_pressures old new
  rw [a,b]; linarith
theorem global_no_exclusive (old new : Fin 9 → ℝ) (hw : 0 ≤ old 1) :
    ¬ ((∃ i ∈ carrier g34a, ∀ j ∈ carrier g34a, cmPressure g34a old new i ≤ cmPressure g34a old new j) ∧
       ∀ i ∈ carrier g34a, (∀ j ∈ carrier g34a, cmPressure g34a old new i ≤ cmPressure g34a old new j) →
         realize g34a i = "ahetɔɔkpʊkɔ") := by
  rintro ⟨⟨i,hi,hm⟩,ho⟩
  have hf : i ∈ fiber g34a "ahetɔɔkpʊkɔ" := by simp [fiber,hi,ho i hi hm]
  rw [bound_readout.1] at hf
  have he : i = 774 := by simpa using hf
  subst i
  have hr : ∀ j ∈ carrier g34a, cmPressure g34a old new 605 ≤ cmPressure g34a old new j :=
    fun j hj => le_trans (global_bound old new hw) (hm j hj)
  have wrong := ho 605 bound_readout.2.2 hr
  rw [bound_readout.2.1] at wrong
  contradiction

theorem ordinary_family_bound {I : Type} [Fintype I] (w : I → ℝ)
    (fGoal fRival : I → ℝ) (m : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, fRival i ≤ fGoal i) :
    m + ∑ i, w i*fRival i ≤ m + ∑ i, w i*fGoal i := by
  exact add_le_add (le_refl m)
    (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hw i)))

def edge (u : Input) (s t : Nat) : Prop :=
  s ∈ carrier u ∧ t ∈ carrier u ∧
  ((coords u s).zip (coords u t)).countP (fun p => p.1 != p.2) = 1
instance (u : Input) (s t : Nat) : Decidable (edge u s t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def Selected {S : Type} (P : S → ℝ) (E : S → S → Prop) (c : ℝ) (s t : S) : Prop :=
  E s t ∧ c + P t < P s ∧ ∀ u, E s u → c + P t ≤ c + P u
inductive Walk {S : Type} (P : S → ℝ) (E : S → S → Prop) (c : ℝ) : Nat → S → S → Prop
  | nil (s) : Walk P E c 0 s s
  | cons {n s t u} : Selected P E c s t → Walk P E c n t u → Walk P E c (n+1) s u
theorem walk_weak {S : Type} {P : S → ℝ} {E c n s t}
    (h : Walk P E c n s t) (hc : 0 ≤ c) : P t ≤ P s := by
  induction h with
  | nil => rfl
  | cons hs _ ih => linarith [hs.2.1]
theorem barrier_no_walk {S : Type} {P : S → ℝ} {E : S → S → Prop}
    {c : ℝ} {start goal rival : S} (hc : 0 ≤ c)
    (hne : start ≠ goal) (he : E start rival) (hnot : ¬E start goal)
    (bound : P rival ≤ P goal) : ∀ n, ¬Walk P E c n start goal := by
  intro n hw
  cases hw with
  | nil => exact hne rfl
  | @cons n _ t _ hs ht =>
    have hm := hs.2.2 rival he
    cases ht with
    | nil => exact hnot hs.1
    | cons hs2 rest =>
      have hd := walk_weak rest hc
      have hstep := hs2.2.1
      linarith
theorem bound_edges : edge g34a 566 605 ∧ ¬edge g34a 566 774 ∧ 566 ≠ 774 ∧
    expand g34a 566 = g34a.origin := by decide
theorem local_no_goal (old new : Fin 9 → ℝ) (c : ℝ)
    (hw : 0 ≤ old 1) (hc : 0 < c) :
    ∀ n, ¬Walk (cmPressure g34a old new) (edge g34a) c n 566 774 :=
  barrier_no_walk (le_of_lt hc) bound_edges.2.2.1 bound_edges.1 bound_edges.2.1
    (global_bound old new hw)
theorem local_no_correct_observation (old new : Fin 9 → ℝ) (c : ℝ)
    (hw : 0 ≤ old 1) (hc : 0 < c) {n i : Nat} (hi : i ∈ carrier g34a)
    (path : Walk (cmPressure g34a old new) (edge g34a) c n 566 i) :
    realize g34a i ≠ "ahetɔɔkpʊkɔ" := by
  intro ho
  have hf : i ∈ fiber g34a "ahetɔɔkpʊkɔ" := by simp [fiber,hi,ho]
  rw [bound_readout.1] at hf
  have he : i = 774 := by simpa using hf
  subst i
  exact local_no_goal old new c hw hc n path

#print axioms bound_goal_counts
#print axioms bound_rival_counts
#print axioms bound_readout
#print axioms global_no_exclusive
#print axioms ordinary_family_bound
#print axioms complete_unique
#print axioms unique_min_observation
#print axioms barrier_no_walk
#print axioms bound_edges
#print axioms local_no_correct_observation
end Retained
