                                                               
import PhonologicalRequirements.Footprint

namespace PhonologicalRequirements.FootprintSupport

variable {N V R F : Type}

def scan (real : N → Option V) (test : N → V → Bool) (stop : Bool) :
    List N → Option (N × V)
  | [] => none
  | n :: ns => match real n with
    | none => scan real test stop ns
    | some v => if test n v then some (n,v)
                else if stop then none else scan real test stop ns

def accept (allowed : N → Bool) : Option (N × V) → Option (N × V)
  | none => none
  | some (n,v) => if allowed n then some (n,v) else none

def resolve (real : N → Option V) (test : N → V → Bool) (stop : Bool)
    (allowed : N → Bool) (order : List N) : Option (N × V) :=
  accept allowed (scan real test stop order)

def Agree (real other : N → Option V) (support : List N) : Prop :=
  ∀ n ∈ support, real n = other n

theorem scan_congr (real other : N → Option V) (test : N → V → Bool)
    (stop : Bool) (order : List N) (h : Agree real other order) :
    scan real test stop order = scan other test stop order := by
  induction order with
  | nil => rfl
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht : Agree real other ns := fun k hk => h k (by simp [hk])
    simp only [scan, hn]
    cases other n with
    | none => exact ih ht
    | some v => simp only; rw [ih ht]

theorem scan_mem (real : N → Option V) (test : N → V → Bool)
    (stop : Bool) (order : List N) {n : N} {v : V}
    (h : scan real test stop order = some (n,v)) : n ∈ order ∧ real n = some v := by
  induction order with
  | nil => cases h
  | cons k ks ih =>
    cases hk : real k with
    | none =>
      simp only [scan, hk] at h
      obtain ⟨hm, hv⟩ := ih h
      exact ⟨by simp [hm], hv⟩
    | some u =>
      simp only [scan, hk] at h
      by_cases ht : test k u = true
      · simp [ht] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp, hk⟩
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
        cases stop with
        | true => cases h
        | false =>
          obtain ⟨hm,hv⟩ := ih h
          exact ⟨by simp [hm],hv⟩

theorem inadmissible_tail (real : N → Option V) (test : N → V → Bool)
    (stop : Bool) (allowed : N → Bool) (order : List N)
    (h : ∀ n ∈ order, allowed n = false) :
    resolve real test stop allowed order = none := by
  unfold resolve
  cases hs : scan real test stop order with
  | none => rfl
  | some p =>
    obtain ⟨n,v⟩ := p
    have hm := (scan_mem real test stop order hs).1
    simp [accept, h n hm]

theorem prefix_suffices (real : N → Option V) (test : N → V → Bool)
    (stop : Bool) (allowed : N → Bool) (pre suffix : List N)
    (h : ∀ n ∈ suffix, allowed n = false) :
    resolve real test stop allowed (pre ++ suffix) =
      resolve real test stop allowed pre := by
  induction pre with
  | nil => simpa [resolve, scan, accept] using inadmissible_tail real test stop allowed suffix h
  | cons n ns ih =>
    simp only [List.cons_append, resolve, scan] at *
    cases hr : real n with
    | none => simpa [hr] using ih
    | some v =>
      by_cases ht : test n v = true
      · simp [hr,ht]
      · cases stop <;> simp_all

theorem prefix_congr (real other : N → Option V) (test : N → V → Bool)
    (stop : Bool) (allowed : N → Bool) (pre suffix : List N)
    (ht : ∀ n ∈ suffix, allowed n = false) (ha : Agree real other pre) :
    resolve real test stop allowed (pre ++ suffix) =
      resolve other test stop allowed (pre ++ suffix) := by
  rw [prefix_suffices real test stop allowed pre suffix ht,
      prefix_suffices other test stop allowed pre suffix ht]
  unfold resolve
  rw [scan_congr real other test stop pre ha]

theorem scoped_congr (real other : N → Option V) (test : N → V → Bool)
    (stop : Bool) (scope allowed : N → Bool) (order : List N)
    (h : ∀ n ∈ order, scope n = true → real n = other n) :
    resolve real test stop allowed (order.filter scope) =
      resolve other test stop allowed (order.filter scope) := by
  unfold resolve
  rw [scan_congr real other test stop (order.filter scope)]
  intro n hn
  have hm := List.mem_filter.mp hn
  exact h n hm.1 hm.2

theorem readers_congr (real other : N → Option V) (test : N → V → Bool)
    (stop : Bool) (allowed : N → Bool) (pre suffix : List N) (anchor : N)
    (read : Option V → Option (N × V) → R)
    (ht : ∀ n ∈ suffix, allowed n = false) (ha : Agree real other pre)
    (hl : real anchor = other anchor) :
    read (real anchor) (resolve real test stop allowed (pre ++ suffix)) =
      read (other anchor) (resolve other test stop allowed (pre ++ suffix)) := by
  rw [hl, prefix_congr real other test stop allowed pre suffix ht ha]

theorem filter_congr (real other : N → Option V) (predicate : N → Option V → Bool)
    (domain : List N) (h : Agree real other domain) :
    domain.filter (fun n => predicate n (real n)) =
      domain.filter (fun n => predicate n (other n)) := by
  induction domain with
  | nil => rfl
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht : Agree real other ns := fun k hk => h k (by simp [hk])
    simp only [List.filter_cons, hn]
    rw [ih ht]

theorem positional_congr (real other : N → Option V) (predicate : N → Option V → Bool)
    (domain : List N) (position : List N → R) (h : Agree real other domain) :
    position (domain.filter (fun n => predicate n (real n))) =
      position (domain.filter (fun n => predicate n (other n))) := by
  rw [filter_congr real other predicate domain h]

theorem full_support_ext (real other : N → Option V) (support : List N)
    (hr : ∀ n, n ∉ support → real n = none)
    (ho : ∀ n, n ∉ support → other n = none)
    (h : Agree real other support) : real = other := by
  funext n
  by_cases hn : n ∈ support
  · exact h n hn
  · rw [hr n hn, ho n hn]

theorem fixed_frame_reader_congr (frame : F) (reader : F → (N → Option V) → R)
    (real other : N → Option V) (support : List N)
    (hr : ∀ n, n ∉ support → real n = none)
    (ho : ∀ n, n ∉ support → other n = none)
    (h : Agree real other support) : reader frame real = reader frame other := by
  rw [full_support_ext real other support hr ho h]

theorem simultaneous_readers_congr {S P : Type}
    (real other : N → Option V) (test : S → N → V → Bool)
    (stop : S → Bool) (allowed : S → N → Bool) (pre suffix : S → List N)
    (anchor : N) (domain : P → List N) (predicate : P → N → Option V → Bool)
    (read : Option V → (S → Option (N × V)) → (P → List N) → R)
    (ht : ∀ s n, n ∈ suffix s → allowed s n = false)
    (ha : ∀ s, Agree real other (pre s))
    (hd : ∀ p, Agree real other (domain p)) (hl : real anchor = other anchor) :
    read (real anchor)
      (fun s => resolve real (test s) (stop s) (allowed s) (pre s ++ suffix s))
      (fun p => (domain p).filter (fun n => predicate p n (real n))) =
    read (other anchor)
      (fun s => resolve other (test s) (stop s) (allowed s) (pre s ++ suffix s))
      (fun p => (domain p).filter (fun n => predicate p n (other n))) := by
  have hs : (fun s => resolve real (test s) (stop s) (allowed s) (pre s ++ suffix s)) =
      (fun s => resolve other (test s) (stop s) (allowed s) (pre s ++ suffix s)) := by
    funext s
    exact prefix_congr real other (test s) (stop s) (allowed s) (pre s) (suffix s) (ht s) (ha s)
  have hp : (fun p => (domain p).filter (fun n => predicate p n (real n))) =
      (fun p => (domain p).filter (fun n => predicate p n (other n))) := by
    funext p
    exact filter_congr real other (predicate p) (domain p) (hd p)
  rw [hl, hs, hp]

theorem external_region_irrelevant (real other : N → Option V)
    (test : N → V → Bool) (stop : Bool) (allowed : N → Bool)
    (region outside₁ outside₂ : List N)
    (h₁ : ∀ n ∈ outside₁, allowed n = false)
    (h₂ : ∀ n ∈ outside₂, allowed n = false) (h : Agree real other region) :
    resolve real test stop allowed (region ++ outside₁) =
      resolve other test stop allowed (region ++ outside₂) := by
  rw [prefix_suffices real test stop allowed region outside₁ h₁,
      prefix_suffices other test stop allowed region outside₂ h₂]
  unfold resolve
  rw [scan_congr real other test stop region h]

end PhonologicalRequirements.FootprintSupport
