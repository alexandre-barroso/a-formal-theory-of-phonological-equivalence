                                                   
import PhonologicalCalculus.Application.ProductComposition

namespace WordProjection

variable {A : Type}

inductive Edit (change : A → A → Prop) (create : A → Prop) : List A → List A → Prop
  | set {x y : A} {xs : List A} : change x y → Edit change create (x :: xs) (y :: xs)
  | insert {x : A} {xs : List A} : create x → Edit change create xs (x :: xs)
  | tail {x : A} {xs ys : List A} : Edit change create xs ys → Edit change create (x :: xs) (x :: ys)

def project (word : Bool) : List (Bool × A) → List A
  | [] => []
  | (w,x) :: xs => if w = word then x :: project word xs else project word xs

def merge (xs ys : List A) : List (Bool × A) :=
  xs.map (fun x => (false,x)) ++ ys.map (fun y => (true,y))

def taggedChange (change : A → A → Prop) (x y : Bool × A) : Prop :=
  x.1 = y.1 ∧ change x.2 y.2

def taggedCreate (create : A → Prop) (x : Bool × A) : Prop := create x.2

theorem project_append (w : Bool) (xs ys : List (Bool × A)) :
    project w (xs ++ ys) = project w xs ++ project w ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨v,x⟩ := x
    simp only [List.cons_append,project]
    split <;> simp_all

theorem project_map (w v : Bool) (xs : List A) :
    project w (xs.map (fun x => (v,x))) = if v = w then xs else [] := by
  induction xs with
  | nil => simp [project]
  | cons x xs ih => simp [project,ih]; split <;> simp_all

theorem project_merge_left (xs ys : List A) : project false (merge xs ys) = xs := by
  simp [merge,project_append,project_map]

theorem project_merge_right (xs ys : List A) : project true (merge xs ys) = ys := by
  simp [merge,project_append,project_map]

theorem edit_append (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) (zs : List A) :
    Edit change create (xs ++ zs) (ys ++ zs) := by
  induction h with
  | set hc => exact .set hc
  | insert hc => exact .insert hc
  | tail _ ih => exact .tail ih

theorem edit_prepend (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) (zs : List A) :
    Edit change create (zs ++ xs) (zs ++ ys) := by
  induction zs with
  | nil => exact h
  | cons z zs ih => exact .tail ih

theorem edit_tag (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) (w : Bool) :
    Edit (taggedChange change) (taggedCreate create)
      (xs.map (fun x => (w,x))) (ys.map (fun y => (w,y))) := by
  induction h with
  | set hc => exact .set ⟨rfl,hc⟩
  | insert hc => exact .insert hc
  | tail _ ih => exact .tail ih

theorem edit_project (change : A → A → Prop) (create : A → Prop)
    {xs ys : List (Bool × A)} (h : Edit (taggedChange change) (taggedCreate create) xs ys) :
    ProductComposition.localStep (Edit change create) (Edit change create)
      (project false xs, project true xs) (project false ys, project true ys) := by
  induction h with
  | @set x y xs hc =>
    obtain ⟨w,x⟩ := x
    obtain ⟨v,y⟩ := y
    obtain ⟨h,hc⟩ := hc
    simp only at h
    subst v
    cases w <;> simp only [project,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
    · exact Or.inl ⟨.set hc,rfl⟩
    · exact Or.inr ⟨rfl,.set hc⟩
  | @insert x xs hc =>
    obtain ⟨w,x⟩ := x
    cases w <;> simp only [project,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
    · exact Or.inl ⟨.insert hc,rfl⟩
    · exact Or.inr ⟨rfl,.insert hc⟩
  | @tail x xs ys _ ih =>
    obtain ⟨w,x⟩ := x
    rcases ih with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · cases w <;> simp only [project,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
      · exact Or.inl ⟨.tail ha,hb⟩
      · exact Or.inl ⟨ha,congrArg (List.cons x) hb⟩
    · cases w <;> simp only [project,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
      · exact Or.inr ⟨congrArg (List.cons x) ha,hb⟩
      · exact Or.inr ⟨ha,.tail hb⟩

theorem edit_merge_left (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) (zs : List A) :
    Edit (taggedChange change) (taggedCreate create) (merge xs zs) (merge ys zs) :=
  edit_append _ _ (edit_tag change create h false) _

theorem edit_merge_right (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) (zs : List A) :
    Edit (taggedChange change) (taggedCreate create) (merge zs xs) (merge zs ys) :=
  edit_prepend _ _ (edit_tag change create h true) _

theorem reachable_project (change : A → A → Prop) (create : A → Prop)
    {xs ys : List (Bool × A)}
    (h : Relation.ReflTransGen (Edit (taggedChange change) (taggedCreate create)) xs ys) :
    Relation.ReflTransGen (Edit change create) (project false xs) (project false ys) ∧
    Relation.ReflTransGen (Edit change create) (project true xs) (project true ys) := by
  apply ProductComposition.reachable_components (Edit change create) (Edit change create)
    (p := (project false xs, project true xs)) (q := (project false ys, project true ys))
  induction h with
  | refl => exact .refl
  | tail _ ht ih => exact ih.tail (edit_project change create ht)

theorem reachable_merge_left (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Relation.ReflTransGen (Edit change create) xs ys) (zs : List A) :
    Relation.ReflTransGen (Edit (taggedChange change) (taggedCreate create)) (merge xs zs) (merge ys zs) := by
  induction h with
  | refl => exact .refl
  | tail _ ht ih => exact ih.tail (edit_merge_left change create ht zs)

theorem reachable_merge_right (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Relation.ReflTransGen (Edit change create) xs ys) (zs : List A) :
    Relation.ReflTransGen (Edit (taggedChange change) (taggedCreate create)) (merge zs xs) (merge zs ys) := by
  induction h with
  | refl => exact .refl
  | tail _ ht ih => exact ih.tail (edit_merge_right change create ht zs)

theorem reachable_merge_iff (change : A → A → Prop) (create : A → Prop)
    (xs xs' ys ys' : List A) :
    Relation.ReflTransGen (Edit (taggedChange change) (taggedCreate create)) (merge xs ys) (merge xs' ys') ↔
    Relation.ReflTransGen (Edit change create) xs xs' ∧ Relation.ReflTransGen (Edit change create) ys ys' := by
  constructor
  · intro h
    simpa only [project_merge_left,project_merge_right] using reachable_project change create h
  · rintro ⟨hl,hr⟩
    exact (reachable_merge_left change create hl ys).trans (reachable_merge_right change create hr xs')

def hasHost (w : Bool) (pre post : List (Bool × A)) : Prop :=
  (∃ x, pre.getLast? = some (w,x)) ∨ (∃ x, post.head? = some (w,x))

theorem left_host (pre post right : List A) (h : pre ++ post ≠ []) :
    hasHost false (pre.map (fun x => (false,x)))
      (post.map (fun x => (false,x)) ++ right.map (fun x => (true,x))) := by
  cases hp : pre.getLast? with
  | some x => exact Or.inl ⟨x,by simp [hp]⟩
  | none =>
    have hn : pre = [] := List.getLast?_eq_none_iff.mp hp
    subst pre
    cases post with
    | nil => exact False.elim (h rfl)
    | cons x xs => exact Or.inr ⟨x,rfl⟩

theorem right_host (left pre post : List A) (h : pre ++ post ≠ []) :
    hasHost true (left.map (fun x => (false,x)) ++ pre.map (fun x => (true,x)))
      (post.map (fun x => (true,x))) := by
  cases post with
  | cons x xs => exact Or.inr ⟨x,rfl⟩
  | nil =>
    cases hp : pre.getLast? with
    | some x => exact Or.inl ⟨x,by simp [hp]⟩
    | none =>
      have hn : pre = [] := List.getLast?_eq_none_iff.mp hp
      subst pre
      exact False.elim (h rfl)

inductive NativeStep (change : A → A → Prop) (create : A → Prop) :
    List (Bool × A) → List (Bool × A) → Prop
  | set (pre post : List (Bool × A)) (x y : Bool × A) :
      taggedChange change x y → NativeStep change create (pre ++ x :: post) (pre ++ y :: post)
  | insert (pre post : List (Bool × A)) (x : Bool × A) :
      taggedCreate create x → hasHost x.1 pre post →
      NativeStep change create (pre ++ post) (pre ++ x :: post)

theorem edit_decompose (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) :
    (∃ pre post x y, xs = pre ++ x :: post ∧ ys = pre ++ y :: post ∧ change x y) ∨
    (∃ pre post x, xs = pre ++ post ∧ ys = pre ++ x :: post ∧ create x) := by
  induction h with
  | @set x y xs hc => exact Or.inl ⟨[],xs,x,y,rfl,rfl,hc⟩
  | @insert x xs hc => exact Or.inr ⟨[],xs,x,rfl,rfl,hc⟩
  | @tail x xs ys _ ih =>
    rcases ih with ⟨pre,post,a,b,hs,ht,hc⟩ | ⟨pre,post,a,hs,ht,hc⟩
    · exact Or.inl ⟨x::pre,post,a,b,by simp [hs],by simp [ht],hc⟩
    · exact Or.inr ⟨x::pre,post,a,by simp [hs],by simp [ht],hc⟩

theorem native_edit (change : A → A → Prop) (create : A → Prop)
    {xs ys : List (Bool × A)} (h : NativeStep change create xs ys) :
    Edit (taggedChange change) (taggedCreate create) xs ys := by
  cases h with
  | set pre post x y hc => exact edit_prepend _ _ (.set hc) pre
  | insert pre post x hc _ => exact edit_prepend _ _ (.insert hc) pre

theorem native_merge_left (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) (hn : xs ≠ []) (zs : List A) :
    NativeStep change create (merge xs zs) (merge ys zs) := by
  rcases edit_decompose change create h with ⟨pre,post,x,y,hs,ht,hc⟩ | ⟨pre,post,x,hs,ht,hc⟩
  · subst xs; subst ys
    simpa [merge,List.map_append,List.append_assoc] using
      NativeStep.set (change:=change) (create:=create) (pre.map (fun a => (false,a)))
        (post.map (fun a => (false,a)) ++ zs.map (fun a => (true,a))) (false,x) (false,y) ⟨rfl,hc⟩
  · subst xs; subst ys
    simpa [merge,List.map_append,List.append_assoc] using
      NativeStep.insert (change:=change) (create:=create) (pre.map (fun a => (false,a)))
        (post.map (fun a => (false,a)) ++ zs.map (fun a => (true,a))) (false,x) hc (left_host pre post zs hn)

theorem native_merge_right (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) (hn : xs ≠ []) (zs : List A) :
    NativeStep change create (merge zs xs) (merge zs ys) := by
  rcases edit_decompose change create h with ⟨pre,post,x,y,hs,ht,hc⟩ | ⟨pre,post,x,hs,ht,hc⟩
  · subst xs; subst ys
    simpa [merge,List.map_append,List.append_assoc] using
      NativeStep.set (change:=change) (create:=create)
        (zs.map (fun a => (false,a)) ++ pre.map (fun a => (true,a)))
        (post.map (fun a => (true,a))) (true,x) (true,y) ⟨rfl,hc⟩
  · subst xs; subst ys
    simpa [merge,List.map_append,List.append_assoc] using
      NativeStep.insert (change:=change) (create:=create)
        (zs.map (fun a => (false,a)) ++ pre.map (fun a => (true,a)))
        (post.map (fun a => (true,a))) (true,x) hc (right_host zs pre post hn)

def Word (A : Type) := {xs : List A // xs ≠ []}

def wordEdit (change : A → A → Prop) (create : A → Prop) (x y : Word A) : Prop :=
  Edit change create x.val y.val

def nativeWordStep (change : A → A → Prop) (create : A → Prop) (p q : Word A × Word A) : Prop :=
  NativeStep change create (merge p.1.val p.2.val) (merge q.1.val q.2.val)

theorem native_word_step_iff (change : A → A → Prop) (create : A → Prop)
    (p q : Word A × Word A) :
    nativeWordStep change create p q ↔
      ProductComposition.localStep (wordEdit change create) (wordEdit change create) p q := by
  constructor
  · intro h
    have hp := edit_project change create (native_edit change create h)
    simp only [project_merge_left,project_merge_right,ProductComposition.localStep] at hp
    rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨ha,Subtype.ext hb⟩
    · exact Or.inr ⟨Subtype.ext ha,hb⟩
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · unfold nativeWordStep
      rw [← hb]
      exact native_merge_left change create ha p.1.property p.2.val
    · unfold nativeWordStep
      rw [← ha]
      exact native_merge_right change create hb p.2.property p.1.val

theorem native_word_reachability (change : A → A → Prop) (create : A → Prop)
    (a a' b b' : Word A) :
    Relation.ReflTransGen (nativeWordStep change create) (a,b) (a',b') ↔
      Relation.ReflTransGen (wordEdit change create) a a' ∧
      Relation.ReflTransGen (wordEdit change create) b b' := by
  have hs : nativeWordStep change create =
      ProductComposition.localStep (wordEdit change create) (wordEdit change create) := by
    funext p q
    exact propext (native_word_step_iff change create p q)
  rw [hs]
  exact ProductComposition.reachable_product _ _ _ _ _ _

end WordProjection
