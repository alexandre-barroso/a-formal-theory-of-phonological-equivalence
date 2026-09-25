                                                   
import PhonologicalCalculus.Application.WordProjection

namespace WordProjection

variable {A : Type}

def Ordered (xs : List (Bool × A)) : Prop :=
  xs.Pairwise (fun x y => x.1 = true → y.1 = true)

theorem ordered_merge (xs ys : List A) : Ordered (merge xs ys) := by
  have ht (zs : List A) : zs.Pairwise (fun _ _ => True) := by
    induction zs with
    | nil => exact .nil
    | cons z zs ih => exact .cons (by simp) ih
  simpa [Ordered, merge, List.pairwise_append, List.pairwise_map] using And.intro (ht xs) (ht ys)

theorem ordered_set (pre post : List (Bool × A)) (x y : Bool × A)
    (hxy : x.1 = y.1) (h : Ordered (pre ++ x :: post)) :
    Ordered (pre ++ y :: post) := by
  simpa only [Ordered, List.pairwise_append, List.pairwise_cons, List.mem_cons,
    forall_eq_or_imp, hxy] using h

theorem ordered_duplicate (pre post : List (Bool × A)) (x y : Bool × A)
    (hxy : x.1 = y.1) (h : Ordered (pre ++ x :: post)) :
    Ordered (pre ++ x :: y :: post) := by
  simp only [Ordered, List.pairwise_append, List.pairwise_cons, List.mem_cons,
    forall_eq_or_imp] at h ⊢
  rcases h with ⟨hp,⟨hx,hpost⟩,hall⟩
  refine ⟨hp,⟨?_,⟨?_,hpost⟩⟩,?_⟩
  · exact ⟨fun ht => hxy ▸ ht,hx⟩
  · simpa only [← hxy] using hx
  · intro z hz
    obtain ⟨h1,h2⟩ := hall z hz
    exact ⟨h1,by simpa only [← hxy] using h1,h2⟩

theorem ordered_insert (pre post : List (Bool × A)) (x : Bool × A)
    (hh : hasHost x.1 pre post) (h : Ordered (pre ++ post)) :
    Ordered (pre ++ x :: post) := by
  rcases hh with ⟨v,hv⟩ | ⟨v,hv⟩
  · obtain ⟨ys,rfl⟩ := List.getLast?_eq_some_iff.mp hv
    simpa only [List.append_assoc,List.singleton_append] using
      ordered_duplicate ys post (x.1,v) x rfl (by simpa only [List.append_assoc,List.singleton_append] using h)
  · obtain ⟨ys,rfl⟩ := List.head?_eq_some_iff.mp hv
    have hx := ordered_set pre ys (x.1,v) x rfl h
    exact ordered_duplicate pre ys x (x.1,v) rfl hx

theorem native_ordered (change : A → A → Prop) (create : A → Prop)
    {xs ys : List (Bool × A)} (h : NativeStep change create xs ys) (hx : Ordered xs) :
    Ordered ys := by
  cases h with
  | set pre post x y hc => exact ordered_set pre post x y hc.1 hx
  | insert pre post x _ hh => exact ordered_insert pre post x hh hx

theorem project_nil (w : Bool) (xs : List (Bool × A))
    (h : ∀ x ∈ xs, x.1 ≠ w) : project w xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [project, if_neg (h x (by simp))]
    exact ih (fun y hy => h y (by simp [hy]))

theorem merge_projects (xs : List (Bool × A)) (h : Ordered xs) :
    merge (project false xs) (project true xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨w,x⟩ := x
    obtain ⟨hall,hxs⟩ := List.pairwise_cons.mp h
    have hm := ih hxs
    cases w
    · simpa [project, merge] using congrArg (List.cons (false,x)) hm
    · have hn : project false xs = [] := project_nil false xs (by
        intro y hy
        have ht : y.1 = true := hall y hy rfl
        simp [ht])
      simpa [project, merge, hn] using congrArg (List.cons (true,x)) hm

theorem edit_target_nonempty (change : A → A → Prop) (create : A → Prop)
    {xs ys : List A} (h : Edit change create xs ys) : ys ≠ [] := by
  cases h <;> simp

theorem native_project_nonempty (change : A → A → Prop) (create : A → Prop)
    {xs ys : List (Bool × A)} (h : NativeStep change create xs ys)
    (hx : project false xs ≠ [] ∧ project true xs ≠ []) :
    project false ys ≠ [] ∧ project true ys ≠ [] := by
  rcases edit_project change create (native_edit change create h) with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · change project true xs = project true ys at hb
    exact ⟨edit_target_nonempty change create ha, hb ▸ hx.2⟩
  · change project false xs = project false ys at ha
    exact ⟨ha ▸ hx.1, edit_target_nonempty change create hb⟩

theorem raw_reachable_invariant (change : A → A → Prop) (create : A → Prop)
    (a b : Word A) {ys : List (Bool × A)}
    (h : Relation.ReflTransGen (NativeStep change create) (merge a.val b.val) ys) :
    Ordered ys ∧ project false ys ≠ [] ∧ project true ys ≠ [] := by
  induction h with
  | refl => exact ⟨ordered_merge _ _,by simpa [project_merge_left] using a.property,
                    by simpa [project_merge_right] using b.property⟩
  | tail _ ht ih => exact ⟨native_ordered change create ht ih.1,
                           native_project_nonempty change create ht ih.2⟩

theorem raw_reachable_exact (change : A → A → Prop) (create : A → Prop)
    (a b : Word A) (ys : List (Bool × A)) :
    Relation.ReflTransGen (NativeStep change create) (merge a.val b.val) ys ↔
      ∃ a' b' : Word A, ys = merge a'.val b'.val ∧
        Relation.ReflTransGen (wordEdit change create) a a' ∧
        Relation.ReflTransGen (wordEdit change create) b b' := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a,b,rfl,.refl,.refl⟩
    | @tail xs ys hprev ht ih =>
      obtain ⟨a0,b0,hrep,ha,hb⟩ := ih
      have hi := raw_reachable_invariant change create a b (hprev.tail ht)
      let a' : Word A := ⟨project false ys,hi.2.1⟩
      let b' : Word A := ⟨project true ys,hi.2.2⟩
      have hm : ys = merge a'.val b'.val := (merge_projects ys hi.1).symm
      have hs : nativeWordStep change create (a0,b0) (a',b') := by
        change NativeStep change create (merge a0.val b0.val) (merge a'.val b'.val)
        simpa only [← hrep, ← hm] using ht
      refine ⟨a',b',hm,?_⟩
      rcases (native_word_step_iff change create (a0,b0) (a',b')).mp hs with ⟨he,eq⟩ | ⟨eq,he⟩
      · change b0 = b' at eq
        exact ⟨ha.tail he,eq ▸ hb⟩
      · change a0 = a' at eq
        exact ⟨eq ▸ ha,hb.tail he⟩
  · rintro ⟨a',b',rfl,ha,hb⟩
    have h := (native_word_reachability change create a a' b b').mpr ⟨ha,hb⟩
    have lift {p q : Word A × Word A}
        (hr : Relation.ReflTransGen (nativeWordStep change create) p q) :
        Relation.ReflTransGen (NativeStep change create) (merge p.1.val p.2.val) (merge q.1.val q.2.val) := by
      induction hr with
      | refl => exact .refl
      | tail _ ht ih => exact ih.tail ht
    exact lift h

end WordProjection
