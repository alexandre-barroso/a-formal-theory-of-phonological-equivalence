import PhonologicalCalculus.Application.Regularity.RuleReaders

namespace UyghurJoint

structure State where
  previous : Bool
  terminal : Option Bool
  suffixPresent : Bool
  suffixClass : Option Bool

def reference (previous old : Bool) : State :=
  ⟨previous, some old, true, none⟩

def candidate (previous old raised suffix : Bool) : State :=
  ⟨previous, if raised then none else some old, true, some suffix⟩

def trigger (s : State) (b : Bool) : Bool :=
  s.terminal.getD s.previous == b

def member (partialAccess : Bool) (s : State) (b : Bool) : Option Bool :=
  if s.suffixPresent then
    if partialAccess then s.suffixClass.map (fun x => x == b)
    else some (s.suffixClass == some b)
  else none

def pressure (partialAccess : Bool) (s : State) (b : Bool) : Bool :=
  RuleReaders.pressure (member partialAccess s b)

def marked (partialAccess : Bool) (s : State) (b : Bool) : Bool :=
  trigger s b && pressure partialAccess s b

noncomputable def harmony (partialAccess : Bool) (H lam : ℝ) (U s : State) : ℝ :=
  RuleReaders.contribution H lam (marked partialAccess U false)
    (trigger s false) (pressure partialAccess s false) +
  RuleReaders.contribution H lam (marked partialAccess U true)
    (trigger s true) (pressure partialAccess s true)

noncomputable def currentHarmony (H : ℝ) (s : State) : ℝ :=
  H * (if marked false s false then 1 else 0) +
  H * (if marked false s true then 1 else 0)

noncomputable def nativeScore (H lam L R : ℝ) (previous old raised suffix : Bool) : ℝ :=
  (if raised then R else L) + harmony false H lam
    (reference previous old) (candidate previous old raised suffix)

noncomputable def normalScore (H lam L R : ℝ) (previous old raised suffix : Bool) : ℝ :=
  (if raised then R else L) +
    (if suffix == old then (if raised && (previous != old) then lam * H else 0) else H)

noncomputable def inputSurfaceScore (a b L R : ℝ) (previous old raised suffix : Bool) : ℝ :=
  (if raised then R else L) + (if suffix == old then 0 else a) +
    (if suffix == (if raised then previous else old) then 0 else b)

theorem initial_total (previous old b : Bool) :
    marked false (reference previous old) b = (old == b) := by
  cases previous <;> cases old <;> cases b <;> rfl

theorem initial_partial (previous old b : Bool) :
    marked true (reference previous old) b = false := by
  cases previous <;> cases old <;> cases b <;> rfl

theorem absent_subject (partialAccess b : Bool) (s : State) (h : s.suffixPresent = false) :
    pressure partialAccess s b = false := by
  simp [pressure, member, h, RuleReaders.pressure]

theorem complete_score (H lam L R : ℝ) (previous old raised suffix : Bool) :
    nativeScore H lam L R previous old raised suffix =
      normalScore H lam L R previous old raised suffix := by
  cases previous <;> cases old <;> cases raised <;> cases suffix <;>
    simp [nativeScore, normalScore, harmony, RuleReaders.contribution,
      marked, trigger, pressure, member, reference, candidate, RuleReaders.pressure] <;> ring

theorem partial_current (H lam : ℝ) (previous old raised suffix : Bool) :
    harmony true H lam (reference previous old) (candidate previous old raised suffix) =
      lam * currentHarmony H (candidate previous old raised suffix) := by
  cases previous <;> cases old <;> cases raised <;> cases suffix <;>
    simp [harmony, currentHarmony, RuleReaders.contribution,
      marked, trigger, pressure, member, reference, candidate, RuleReaders.pressure] <;> ring

theorem gauge_shift (H lam L R : ℝ) (previous old raised suffix : Bool) :
    nativeScore H lam L R previous old raised suffix - L =
      nativeScore H lam 0 (R-L) previous old raised suffix := by
  simp only [nativeScore]
  cases raised <;> simp <;> ring

theorem matched_rival_offset (H lam L R : ℝ) (previous old raised suffix : Bool) :
    nativeScore H lam L R previous old raised suffix =
      inputSurfaceScore (H - lam*H/2) (lam*H/2) L R previous old raised suffix +
        (if raised && (previous != old) then lam*H/2 else 0) := by
  rw [complete_score]
  cases previous <;> cases old <;> cases raised <;> cases suffix <;>
    simp [normalScore, inputSurfaceScore] <;> ring

theorem unraised_gap (H lam L R : ℝ) (previous old : Bool) :
    nativeScore H lam L R previous old false (!old) -
      nativeScore H lam L R previous old false old = H := by
  simp only [complete_score]
  cases previous <;> cases old <;> simp [normalScore] <;> ring

theorem raised_gap (H lam L R : ℝ) (previous old : Bool) :
    nativeScore H lam L R previous old true (!old) -
      nativeScore H lam L R previous old true old =
        (if previous == old then H else H - lam*H) := by
  simp only [complete_score]
  cases previous <;> cases old <;> simp [normalScore] <;> ring

theorem gaps_identify (H1 H2 lam1 lam2 : ℝ) (h : H1 ≠ 0)
    (hU : H1 = H2) (hR : H1-lam1*H1 = H2-lam2*H2) :
    H1 = H2 ∧ lam1 = lam2 := by
  subst H2
  constructor
  · rfl
  · apply (mul_right_cancel₀ h)
    linarith

theorem zero_weight (lam L R : ℝ) (previous old raised suffix : Bool) :
    nativeScore 0 lam L R previous old raised suffix = if raised then R else L := by
  rw [complete_score]
  cases previous <;> cases old <;> cases raised <;> cases suffix <;> simp [normalScore]

theorem nonnegative_representative (d : ℝ) :
    0 ≤ max d 0 ∧ 0 ≤ max (-d) 0 ∧ max d 0 - max (-d) 0 = d := by
  constructor
  · exact le_max_right _ _
  constructor
  · exact le_max_right _ _
  by_cases h : 0 ≤ d
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

end UyghurJoint
