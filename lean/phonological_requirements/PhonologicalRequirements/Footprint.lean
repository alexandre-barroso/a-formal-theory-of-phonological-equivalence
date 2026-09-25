                                                                                                           
namespace PhonologicalRequirements
namespace Footprint

variable {V : Type}

def scan (f : Nat → Option V) (adm : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, j => match f j with
    | some _ => if adm j then some j else scan f adm fuel (j + 1)
    | none => scan f adm fuel (j + 1)

def resolveDyn (f : Nat → Option V) (n i far : Nat) (adm : Nat → Bool) : Option Nat :=
  match scan f (fun _ => true) n (i + 1) with
  | some j => if j ≤ far ∧ adm j then some j else none
  | none => none

def resolveIn (f : Nat → Option V) (n i : Nat) (adm : Nat → Bool) : Option Nat :=
  scan f adm n (i + 1)

def AgreeOn (f g : Nat → Option V) (i far : Nat) : Prop :=
  ∀ j, i < j → j ≤ far → f j = g j

def trunc (far : Nat) : Option Nat → Option Nat
  | some j => if j ≤ far then some j else none
  | none => none

theorem scan_congr (f g : Nat → Option V) (adm : Nat → Bool) (far : Nat) :
    ∀ fuel j, (∀ k, j ≤ k → k ≤ far → f k = g k) →
      trunc far (scan f adm fuel j) = trunc far (scan g adm fuel j) := by
  intro fuel
  induction fuel with
  | zero => intro j _; rfl
  | succ m ih =>
    intro j h
    by_cases hj : j ≤ far
    · have hfg : f j = g j := h j (Nat.le_refl j) hj
      have h' : ∀ k, j + 1 ≤ k → k ≤ far → f k = g k := fun k hk hkf => h k (Nat.le_of_succ_le hk) hkf
      simp only [scan]
      rw [hfg]
      cases g j with
      | some v =>
        simp only
        by_cases ha : adm j
        · simp [ha]
        · simp [ha]; exact ih (j + 1) h'
      | none =>
        simp only
        exact ih (j + 1) h'
    ·
      have key : ∀ (h : Nat → Option V) (fuel : Nat) (k : Nat), far < k → trunc far (scan h adm fuel k) = none := by
        intro h fuel
        induction fuel with
        | zero => intro k _; rfl
        | succ m' ih' =>
          intro k hk
          simp only [scan]
          cases h k with
          | some v =>
            simp only
            by_cases ha : adm k
            · simp [ha, trunc, Nat.not_le.mpr hk]
            · simp [ha]; exact ih' (k + 1) (Nat.lt_succ_of_lt hk)
          | none =>
            simp only
            exact ih' (k + 1) (Nat.lt_succ_of_lt hk)
      rw [key f (m + 1) j (Nat.lt_of_not_le hj), key g (m + 1) j (Nat.lt_of_not_le hj)]

theorem resolveDyn_congr (f g : Nat → Option V) (n i far : Nat) (adm : Nat → Bool)
    (h : AgreeOn f g i far) : resolveDyn f n i far adm = resolveDyn g n i far adm := by
  have hs := scan_congr f g (fun _ => true) far n (i + 1) (fun k hk hkf => h k (Nat.lt_of_succ_le hk) hkf)
  unfold resolveDyn
  revert hs
  cases scan f (fun _ => true) n (i + 1) with
  | none =>
    cases scan g (fun _ => true) n (i + 1) with
    | none => intro _; rfl
    | some j =>
      intro hs
      simp only [trunc] at hs
      by_cases hj : j ≤ far
      · simp [hj] at hs
      · simp [hj]
  | some j =>
    cases scan g (fun _ => true) n (i + 1) with
    | none =>
      intro hs
      simp only [trunc] at hs
      by_cases hj : j ≤ far
      · simp [hj] at hs
      · simp [hj]
    | some k =>
      intro hs
      simp only [trunc] at hs
      by_cases hj : j ≤ far <;> by_cases hk : k ≤ far
      · simp [hj, hk] at hs; subst hs; rfl
      · simp [hj, hk] at hs
      · simp [hj, hk] at hs
      · simp [hj, hk]

theorem resolveIn_congr (f g : Nat → Option V) (n i far : Nat) (adm : Nat → Bool)
    (hadm : ∀ k, adm k = true → k ≤ far) (h : AgreeOn f g i far) :
    resolveIn f n i adm = resolveIn g n i adm := by
  have hs := scan_congr f g adm far n (i + 1) (fun k hk hkf => h k (Nat.lt_of_succ_le hk) hkf)
  have key : ∀ (h : Nat → Option V) (fuel k : Nat), trunc far (scan h adm fuel k) = scan h adm fuel k := by
    intro h fuel
    induction fuel with
    | zero => intro k; rfl
    | succ m ih =>
      intro k
      simp only [scan]
      cases h k with
      | some v =>
        simp only
        by_cases ha : adm k = true
        · simp [ha, trunc, hadm k ha]
        · simp [ha]; exact ih (k + 1)
      | none => simp only; exact ih (k + 1)
  unfold resolveIn
  rw [← key f n (i + 1), ← key g n (i + 1)]
  exact hs

theorem scan_ge (f : Nat → Option V) (adm : Nat → Bool) :
    ∀ fuel start r, scan f adm fuel start = some r → start ≤ r := by
  intro fuel
  induction fuel with
  | zero => intro start r h; cases h
  | succ m ih =>
    intro start r h
    cases hf : f start with
    | some v =>
      simp only [scan, hf] at h
      by_cases ha : adm start = true
      · simp [ha] at h; subst h; exact Nat.le_refl _
      · simp [ha] at h; exact Nat.le_of_succ_le (ih _ _ h)
    | none =>
      simp only [scan, hf] at h
      exact Nat.le_of_succ_le (ih _ _ h)

theorem readers_congr {R : Type} (f g : Nat → Option V) (n i far : Nat) (adm : Nat → Bool)
    (read : Option V → Option (Option V) → R) (h : AgreeOn f g i far) (hi : f i = g i) :
    read (f i) ((resolveDyn f n i far adm).map f) = read (g i) ((resolveDyn g n i far adm).map g) := by
  rw [hi, resolveDyn_congr f g n i far adm h]
  cases hr : resolveDyn g n i far adm with
  | none => rfl
  | some j =>
    have hj : i < j ∧ j ≤ far := by
      unfold resolveDyn at hr
      revert hr
      cases hs : scan g (fun _ => true) n (i + 1) with
      | none => intro hr; cases hr
      | some k =>
        intro hr
        by_cases hk : k ≤ far ∧ adm k = true
        · simp [hk] at hr; subst hr
          refine ⟨?_, hk.1⟩
          exact Nat.lt_of_succ_le (scan_ge g (fun _ => true) n (i + 1) k hs)
        · simp [hk] at hr
    simp only [Option.map]
    rw [h j hj.1 hj.2]

def narrowA : Nat → Option Bool := fun j => if j = 0 then some false else if j = 1 then some false else if j = 2 then some true else none
def narrowB : Nat → Option Bool := fun j => if j = 0 then some false else if j = 2 then some true else none
def narrowAdm : Nat → Bool := fun j => j == 2

                            
theorem narrow_footprint_unsound :
    narrowA 0 = narrowB 0 ∧ narrowA 2 = narrowB 2 ∧
    resolveDyn narrowA 3 0 2 narrowAdm = none ∧ resolveDyn narrowB 3 0 2 narrowAdm = some 2 := by
  decide

end Footprint
end PhonologicalRequirements
