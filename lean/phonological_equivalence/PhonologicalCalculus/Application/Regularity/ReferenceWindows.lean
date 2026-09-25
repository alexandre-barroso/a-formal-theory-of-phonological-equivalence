                     
                   
import Mathlib.Tactic
import Mathlib.Computability.NFA

namespace ReferenceWindows

structure Window (S : Type) where
  l₂ : Option S
  l₁ : Option S
  c : S
  r₁ : Option S
  r₂ : Option S
  deriving DecidableEq, Fintype

def mirror {S : Type} (w : Window S) : Window S := ⟨w.r₂,w.r₁,w.c,w.l₁,w.l₂⟩

def leftOK {S : Type} : Option S → Option S → List (Window S) → Prop
  | _, _, [] => True
  | a, b, w :: xs => w.l₂ = a ∧ w.l₁ = b ∧ leftOK b (some w.c) xs

def valid {S : Type} (xs : List (Window S)) : Prop :=
  leftOK none none xs ∧ leftOK none none (xs.reverse.map mirror)

noncomputable def leftDFA (S : Type) : DFA (Window S) (Option (Option S × Option S)) := by
  classical
  exact {
    start := some (none,none)
    step := fun s w => match s with
      | none => none
      | some (a,b) => if w.l₂ = a ∧ w.l₁ = b then some (b,some w.c) else none
    accept := {s | s.isSome}}

theorem dead {S : Type} (xs : List (Window S)) : (leftDFA S).evalFrom none xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [DFA.evalFrom_cons,leftDFA] using ih

theorem left_correct {S : Type} (xs : List (Window S)) (a b : Option S) :
    (leftDFA S).evalFrom (some (a,b)) xs ∈ (leftDFA S).accept ↔ leftOK a b xs := by
  classical
  induction xs generalizing a b with
  | nil => simp [DFA.evalFrom,leftDFA,leftOK]
  | cons w xs ih =>
    simp only [DFA.evalFrom_cons]
    change ((leftDFA S).evalFrom (if w.l₂ = a ∧ w.l₁ = b then some (b,some w.c) else none) xs).isSome ↔ _
    split_ifs with h
    · have hh := ih b (some w.c)
      change (((leftDFA S).evalFrom (some (b,some w.c)) xs).isSome = true ↔ _) at hh
      simpa [leftOK,h.1,h.2] using hh
    · simp only [dead,Option.isSome_none,Bool.false_eq_true,false_iff,leftOK]
      tauto

theorem regular_left [Finite S] : Language.IsRegular {xs : List (Window S) | leftOK none none xs} := by
  classical
  letI := Fintype.ofFinite S
  refine ⟨_,inferInstance,leftDFA S,?_⟩
  ext xs
  exact left_correct xs none none

theorem regular_comap {A B : Type} {L : Language B} (h : L.IsRegular) (f : A → B) :
    Language.IsRegular {xs | xs.map f ∈ L} := by
  rcases h with ⟨Q,hQ,M,rfl⟩
  exact ⟨Q,hQ,M.comap f,M.accepts_comap f⟩

theorem regular_valid [Finite S] : Language.IsRegular {xs : List (Window S) | valid xs} := by
  have h := (regular_comap (regular_left (S := S)) mirror).reverse
  have hi := (regular_left (S := S)).inf h
  convert hi using 1
  ext xs
  rfl

theorem left_unique {S : Type} {xs ys : List (Window S)} {a b : Option S}
    (hx : leftOK a b xs) (hy : leftOK a b ys) (hc : xs.map Window.c = ys.map Window.c) :
    xs.map (fun w => (w.l₂,w.l₁,w.c)) = ys.map (fun w => (w.l₂,w.l₁,w.c)) := by
  induction xs generalizing ys a b with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hc
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at hc ⊢
      rcases hx with ⟨hx₂,hx₁,hxt⟩
      rcases hy with ⟨hy₂,hy₁,hyt⟩
      refine ⟨by simp [hx₂,hx₁,hy₂,hy₁,hc.1],?_⟩
      apply ih hxt
      · simpa [hc.1] using hyt
      · exact hc.2

theorem window_unique {S : Type} {xs ys : List (Window S)} (hx : valid xs) (hy : valid ys)
    (hc : xs.map Window.c = ys.map Window.c) : xs = ys := by
  have hl := left_unique hx.1 hy.1 hc
  have hcr : (xs.reverse.map mirror).map Window.c = (ys.reverse.map mirror).map Window.c := by
    simpa [List.map_map,mirror,List.map_reverse,Function.comp_def] using congrArg List.reverse hc
  have hr := left_unique hx.2 hy.2 hcr
  have hr' : xs.map (fun w => (w.r₂,w.r₁,w.c)) = ys.map (fun w => (w.r₂,w.r₁,w.c)) := by
    simpa [List.map_map,mirror,List.map_reverse,Function.comp_def] using congrArg List.reverse hr
  clear hx hy hc hcr hr
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at hl hr'
      have he : x = y := by
        cases x; cases y
        simp only [Prod.mk.injEq] at hl hr'
        simp_all
      exact congrArg₂ List.cons he (ih hl.2 hr'.2)

def endPair {S : Type} (a b : Option S) (xs : List (Window S)) : Option S × Option S :=
  xs.foldl (fun p w => (p.2,some w.c)) (a,b)

theorem left_append {S : Type} (a b : Option S) (xs ys : List (Window S)) :
    leftOK a b (xs ++ ys) ↔ leftOK a b xs ∧ leftOK (endPair a b xs).1 (endPair a b xs).2 ys := by
  induction xs generalizing a b with
  | nil => simp [leftOK,endPair]
  | cons w xs ih => simp [leftOK,endPair,ih,and_assoc]

theorem end_reverse {S : Type} (xs : List (Window S)) :
    endPair none none (xs.reverse.map mirror) =
      ((xs.tail.head?).map Window.c,xs.head?.map Window.c) := by
  cases xs with
  | nil => rfl
  | cons a xs => cases xs with
    | nil => rfl
    | cons b xs =>
      simp [endPair,List.reverse_cons,List.map_append,List.foldl_append,mirror]

def rightOK {S : Type} : List (Window S) → Prop
  | [] => True
  | w :: xs => w.r₁ = xs.head?.map Window.c ∧ w.r₂ = xs.tail.head?.map Window.c ∧ rightOK xs

theorem right_to_reverse {S : Type} {xs : List (Window S)} (h : rightOK xs) :
    leftOK none none (xs.reverse.map mirror) := by
  induction xs with
  | nil => trivial
  | cons w xs ih =>
    rcases h with ⟨hr₁,hr₂,ht⟩
    simp only [List.reverse_cons,List.map_append,List.map_singleton,left_append]
    refine ⟨ih ht,?_⟩
    rw [end_reverse]
    simpa [leftOK,mirror] using And.intro hr₂ hr₁

def annotate {S : Type} (a b : Option S) : List S → List (Window S)
  | [] => []
  | c :: xs => ⟨a,b,c,xs.head?,xs.tail.head?⟩ :: annotate b (some c) xs

theorem annotate_centers {S : Type} (xs : List S) (a b : Option S) :
    (annotate a b xs).map Window.c = xs := by
  induction xs generalizing a b with
  | nil => rfl
  | cons c xs ih => simp [annotate,ih]

theorem annotate_left {S : Type} (xs : List S) (a b : Option S) :
    leftOK a b (annotate a b xs) := by
  induction xs generalizing a b with
  | nil => trivial
  | cons c xs ih => exact ⟨rfl,rfl,ih _ _⟩

theorem annotate_right {S : Type} (xs : List S) (a b : Option S) :
    rightOK (annotate a b xs) := by
  induction xs generalizing a b with
  | nil => trivial
  | cons c xs ih =>
    refine ⟨?_,?_,ih _ _⟩
    · cases xs <;> rfl
    · cases xs with
      | nil => rfl
      | cons d ys => cases ys <;> rfl

theorem annotate_valid {S : Type} (xs : List S) : valid (annotate none none xs) :=
  ⟨annotate_left xs none none,right_to_reverse (annotate_right xs none none)⟩

theorem valid_iff_canonical {S : Type} (xs : List (Window S)) :
    valid xs ↔ xs = annotate none none (xs.map Window.c) := by
  constructor
  · intro h
    exact window_unique h (annotate_valid _) (annotate_centers _ _ _).symm
  · intro h
    rw [h]
    exact annotate_valid _

end ReferenceWindows
