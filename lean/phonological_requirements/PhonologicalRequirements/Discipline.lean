                                       
namespace PhonologicalRequirements
namespace Discipline

inductive Role where
  | subject | trigger
deriving DecidableEq, Repr

inductive Kind where
  | anchor | step | stepof | search | assoc | assocof | corr
deriving DecidableEq, Repr

structure Slot where
  name       : String
  sort       : String
  role       : Role
  kind       : Kind
  relation   : Option String
  scope      : String
  direction  : Int
  filter     : Option String
  filterMode : String
  policy     : String
  coord      : List (String × String)
deriving DecidableEq, Repr

structure Decl where
  slots      : List Slot
  actSlots   : List String
  consSlots  : List String
  override   : Bool
deriving Repr

def Slot.total (totalSort : String → Bool) (s : Slot) : Bool :=
  s.kind == .anchor && totalSort s.sort

def Slot.key (s : Slot) : Kind × Option String × Int × Option String := (s.kind, s.relation, s.direction, s.filter)
def Slot.how (s : Slot) : String × String × String × List (String × String) :=
  (s.scope, s.policy, s.filterMode, s.coord)

def declared (d : Decl) (n : String) : Bool := d.slots.any (fun s => s.name == n)
def lookup (d : Decl) (n : String) : Option Slot := d.slots.find? (fun s => s.name == n)

def R1 (d : Decl) : Prop := ∀ n, n ∈ d.actSlots ++ d.consSlots → declared d n = true
def R2 (d : Decl) : Prop := ∀ s, s ∈ d.slots → s.name ∈ d.consSlots → s.role = .subject
def Slot.isLink (s : Slot) : Bool := s.kind == .assoc || s.kind == .assocof || s.kind == .corr

def R3 (totalSort : String → Bool) (d : Decl) : Prop :=
  ∀ s, s ∈ d.slots → s.name ∈ d.consSlots → s.total totalSort = false → s.isLink = false → s.scope ≠ "unscoped"
def R4 (d : Decl) : Prop :=
  ∀ s, s ∈ d.slots → ∀ t, t ∈ d.slots → s.kind ≠ .anchor → t.kind ≠ .anchor → s.key = t.key → s.how = t.how
def R5 (d : Decl) : Prop := d.override = false

def Rules (totalSort : String → Bool) (d : Decl) : Prop :=
  R1 d ∧ R2 d ∧ R3 totalSort d ∧ R4 d ∧ R5 d

def check1 (d : Decl) : Bool := (d.actSlots ++ d.consSlots).all (fun n => declared d n)
def check2 (d : Decl) : Bool := d.slots.all (fun s => !(decide (s.name ∈ d.consSlots)) || decide (s.role = .subject))
def check3 (totalSort : String → Bool) (d : Decl) : Bool :=
  d.slots.all (fun s => !(decide (s.name ∈ d.consSlots)) || s.total totalSort || s.isLink || decide (s.scope ≠ "unscoped"))
def check4 (d : Decl) : Bool :=
  d.slots.all (fun s => d.slots.all (fun t =>
    decide (s.kind = .anchor) || decide (t.kind = .anchor) || !(decide (s.key = t.key)) || decide (s.how = t.how)))
def check5 (d : Decl) : Bool := !d.override

def wellTyped (totalSort : String → Bool) (d : Decl) : Bool :=
  check1 d && check2 d && check3 totalSort d && check4 d && check5 d

theorem check1_iff (d : Decl) : check1 d = true ↔ R1 d := by
  unfold check1 R1
  rw [List.all_eq_true]

instance (d : Decl) : Decidable (R1 d) := decidable_of_iff _ (check1_iff d)

theorem check2_iff (d : Decl) : check2 d = true ↔ R2 d := by
  unfold check2 R2
  rw [List.all_eq_true]
  constructor
  · intro h s hs hn
    have := h s hs
    simp [hn] at this
    exact this
  · intro h s hs
    by_cases hn : s.name ∈ d.consSlots
    · simp [hn, h s hs hn]
    · simp [hn]

instance (d : Decl) : Decidable (R2 d) := decidable_of_iff _ (check2_iff d)

theorem check3_iff (t : String → Bool) (d : Decl) : check3 t d = true ↔ R3 t d := by
  unfold check3 R3
  rw [List.all_eq_true]
  constructor
  · intro h s hs hn htot hk
    have := h s hs
    simp [hn, htot, hk] at this
    exact this
  · intro h s hs
    by_cases hn : s.name ∈ d.consSlots
    · by_cases htot : s.total t = true
      · simp [htot]
      · have htot' : s.total t = false := by cases hx : s.total t <;> simp_all
        by_cases hk : s.isLink = true
        · simp [hk]
        · have hk' : s.isLink = false := by cases hx : s.isLink <;> simp_all
          simp [hn, htot', hk', h s hs hn htot' hk']
    · simp [hn]

instance (t : String → Bool) (d : Decl) : Decidable (R3 t d) := decidable_of_iff _ (check3_iff t d)

theorem check4_iff (d : Decl) : check4 d = true ↔ R4 d := by
  unfold check4 R4
  rw [List.all_eq_true]
  constructor
  · intro h s hs u hu hks hku hkey
    have := h s hs
    rw [List.all_eq_true] at this
    have := this u hu
    simp [hks, hku, hkey] at this
    exact this
  · intro h s hs
    rw [List.all_eq_true]
    intro u hu
    by_cases hks : s.kind = .anchor
    · simp [hks]
    · by_cases hku : u.kind = .anchor
      · simp [hku]
      · by_cases hkey : s.key = u.key
        · simp [hks, hku, hkey, h s hs u hu hks hku hkey]
        · simp [hkey]

instance (d : Decl) : Decidable (R4 d) := decidable_of_iff _ (check4_iff d)

theorem check5_iff (d : Decl) : check5 d = true ↔ R5 d := by
  unfold check5 R5
  cases d.override <;> simp

instance (d : Decl) : Decidable (R5 d) := decidable_of_iff _ (check5_iff d)

theorem wellTyped_iff (t : String → Bool) (d : Decl) : wellTyped t d = true ↔ Rules t d := by
  unfold wellTyped Rules
  simp only [Bool.and_eq_true]
  rw [check1_iff, check2_iff, check3_iff, check4_iff, check5_iff]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

instance (t : String → Bool) (d : Decl) : Decidable (Rules t d) := decidable_of_iff _ (wellTyped_iff t d)

def totalOr : String → Bool := fun s => s == "Or"

def anchorT : Slot := ⟨"t", "Or", .subject, .anchor, none, "unscoped", 1, none, "skip", "dynamic", []⟩

def guaA : Decl :=
  { slots := [anchorT,
              ⟨"n_guarded", "Rel", .trigger, .step, some "succ", "next_word", 1, none, "skip", "dynamic", []⟩,
              ⟨"n_free",    "Rel", .subject, .step, some "succ", "unscoped",  1, none, "skip", "dynamic", []⟩],
    actSlots := ["t", "n_guarded"], consSlots := ["t", "n_free"], override := true }

def guaA_typed : Decl :=
  { slots := [anchorT, ⟨"n", "Rel", .subject, .step, some "succ", "next_word", 1, none, "skip", "dynamic", []⟩],
    actSlots := ["t", "n"], consSlots := ["t", "n"], override := false }

def lithR : Decl :=
  { slots := [anchorT, ⟨"n", "Rel", .subject, .step, some "succ", "same_prosodic_word", 1, none, "skip", "dynamic", []⟩],
    actSlots := ["t", "n"], consSlots := ["t", "n"], override := false }

def lithS : Decl :=
  { slots := [anchorT,
              ⟨"n",  "Rel", .trigger, .step, some "succ", "same_prosodic_word", 1, none, "skip", "dynamic", []⟩,
              ⟨"n2", "Or",  .subject, .step, some "succ", "same_prosodic_word", 1, none, "skip", "origin_bound", []⟩],
    actSlots := ["t", "n"], consSlots := ["t", "n2"], override := true }

theorem guaA_rejected : wellTyped totalOr guaA = false := by decide
theorem guaA_rule2 : ¬ R2 guaA ∨ ¬ R3 totalOr guaA := by
  right; decide
theorem guaA_three_grounds : ¬ R3 totalOr guaA ∧ ¬ R4 guaA ∧ ¬ R5 guaA := by decide
theorem guaA_rules12 : R1 guaA ∧ R2 guaA := by decide
theorem guaA_typed_accepted : wellTyped totalOr guaA_typed = true := by decide
theorem lithR_accepted : wellTyped totalOr lithR = true := by decide
theorem lithS_rejected : wellTyped totalOr lithS = false := by decide
theorem lithS_grounds : ¬ R4 lithS ∧ ¬ R5 lithS ∧ R1 lithS ∧ R2 lithS ∧ R3 totalOr lithS := by decide

def factorizationAccepted (a b : Decl) : Bool := wellTyped totalOr a && wellTyped totalOr b
theorem factorizations : factorizationAccepted lithR lithR = true ∧ factorizationAccepted lithR lithS = false ∧
    factorizationAccepted lithS lithR = false ∧ factorizationAccepted lithS lithS = false := by decide

end Discipline
end PhonologicalRequirements
