                  
                   
import PhonologicalCalculus.Application.Regularity.Irrational.Negative

namespace NativeIrrational

def gen : List Bool → List (List (Bool × Bool))
  | [] => [[]]
  | x::xs => (gen xs).map (fun w => (x,false)::w) ++ (gen xs).map (fun w => (x,true)::w)

theorem mem_gen_iff (u : List Bool) (w : List (Bool × Bool)) : w ∈ gen u ↔ input w=u := by
  induction u generalizing w with
  | nil => simp [gen,input]
  | cons x xs ih =>
    cases w with
    | nil => simp [gen,input]
    | cons xy w =>
      obtain ⟨z,b⟩ := xy
      cases b <;> simp [gen,input,List.mem_map,ih,input,and_comm,eq_comm]

theorem gen_count (u : List Bool) : (gen u).length = 2^u.length := by
  induction u with
  | nil => simp [gen]
  | cons x xs ih => simp [gen,ih,pow_succ]; omega

theorem observer_recovers_alignment (w v : List (Bool × Bool))
    (hi : input w=input v) (ho : output w=output v) : w=v := by
  induction w generalizing v with
  | nil => simpa [input] using hi.symm
  | cons xy w ih =>
    cases v with
    | nil => simp [input] at hi
    | cons zz v =>
      obtain ⟨x,y⟩ := xy
      obtain ⟨z,t⟩ := zz
      simp only [input,List.map_cons,List.cons.injEq] at hi
      simp only [output,List.map_cons,List.cons.injEq] at ho
      have hw := ih v hi.2 ho.2
      simp [hi.1,ho.1,hw]

noncomputable def nativeRun (p : (Option Bool × Option Bool) × ℝ) (xy : Bool × Bool) :
    (Option Bool × Option Bool) × ℝ :=
  ((some xy.1,some xy.2),p.2+nativeLocal p.1.1 p.1.2 xy.1 xy.2)
noncomputable def nativeScore (w : List (Bool × Bool)) : ℝ :=
  (w.foldl nativeRun ((none,none),0)).2

theorem native_fold_exact (w : List (Bool × Bool))
    (rp cp : Option Bool) (c : ℝ) :
    let p := w.foldl nativeRun ((rp,cp),c)
    (p.1.2,p.2) = w.foldl run (cp,c) := by
  induction w generalizing rp cp c with
  | nil => rfl
  | cons xy w ih =>
    obtain ⟨x,y⟩ := xy
    simp only [List.foldl_cons,nativeRun,run]
    rw [native_local_exact]
    simpa only [add_assoc] using ih (some x) (some y) (c+unary x y+switch cp y)

theorem native_score_exact (w : List (Bool × Bool)) : nativeScore w=score w := by
  exact congrArg Prod.snd (native_fold_exact w none none 0)

def nativeWinnerLanguage : Language (Bool × Bool) :=
  {w | ∀ v ∈ gen (input w), nativeScore w ≤ nativeScore v}

theorem native_winner_language_exact : nativeWinnerLanguage=winnerLanguage := by
  ext w
  change (∀ v ∈ gen (input w), nativeScore w ≤ nativeScore v) ↔ _
  simp only [mem_gen_iff,native_score_exact]
  rfl

theorem native_full_argmin_nonregular : ¬ nativeWinnerLanguage.IsRegular := by
  rw [native_winner_language_exact]
  exact full_winner_relation_nonregular

theorem native_minimum_exact (u : List Bool) :
    (∃ w ∈ gen u, nativeScore w=minimum u) ∧
    ∀ w ∈ gen u, minimum u ≤ nativeScore w := by
  simp only [mem_gen_iff,native_score_exact]
  exact minimum_exact u

theorem native_no_finite_weighted_machine {Q : Type} [Finite Q] (M : WeightedMachine Q) :
    ¬ (∀ u, (∃ w ∈ gen u, nativeScore w=M.value u) ∧ ∀ w ∈ gen u, M.value u ≤ nativeScore w) := by
  intro h
  apply no_finite_weighted_machine M
  intro u
  obtain ⟨v,hv,hvc⟩ := (h u).1
  obtain ⟨w,hw,hwc⟩ := (native_minimum_exact u).1
  apply le_antisymm
  · rw [← hwc]; exact (h u).2 w hw
  · rw [← hvc]; exact (native_minimum_exact u).2 v hv
end NativeIrrational
