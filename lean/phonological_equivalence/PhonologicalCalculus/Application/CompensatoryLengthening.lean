        
import PhonologicalCalculus.Application.AccentRegion

namespace CompensatoryLengthening

abbrev Candidate := Bool × Option Bool

def generate (total : Bool) : List Candidate :=
  [false, true].flatMap fun deleted =>
    (if !total && deleted then [none] else [some true, some false, none]).map
      fun host => (deleted, host)

def admissible (total : Bool) (c : Candidate) : Prop :=
  !total && c.1 = true → c.2 = none

instance (total : Bool) (c : Candidate) : Decidable (admissible total c) :=
  inferInstanceAs (Decidable (_ → _))

def hasMora (total : Bool) (c : Candidate) : Bool := total || !c.1

def linkedV (total : Bool) (c : Candidate) : Bool :=
  hasMora total c && c.2 == some true

def linkedC (total : Bool) (c : Candidate) : Bool :=
  hasMora total c && c.2 == some false

def coefficients (total : Bool) (c : Candidate) : Nat × Nat × Nat × Nat :=
  (if c.1 then 1 else 0, if c.1 then 0 else 1,
   if hasMora total c && !(linkedV total c || (linkedC total c && !c.1)) then 1 else 0,
   if hasMora total c && !linkedC total c then 1 else 0)

def surface (total : Bool) (c : Candidate) : String :=
  "ti" ++ (if linkedV total c then "ː" else "") ++ (if c.1 then "" else "k")

def compensates (total : Bool) (c : Candidate) : Prop :=
  c.1 = true ∧ linkedV total c = true

instance (total : Bool) (c : Candidate) : Decidable (compensates total c) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Weights where
  max : ℝ
  nocoda : ℝ
  mora : ℝ
  maxlink : ℝ

def nonnegative (w : Weights) : Prop :=
  0 ≤ w.max ∧ 0 ≤ w.nocoda ∧ 0 ≤ w.mora ∧ 0 ≤ w.maxlink

noncomputable def score (total : Bool) (w : Weights) (l : ℝ) (c : Candidate) : ℝ :=
  let q := coefficients total c
  q.1*w.max + q.2.1*w.nocoda + q.2.2.1*l*w.mora + q.2.2.2*w.maxlink

def selects (total : Bool) (w : Weights) (l : ℝ) (good : Candidate → Prop) : Prop :=
  ∀ a ∈ generate total, (∀ b ∈ generate total, score total w l a ≤ score total w l b) → good a

theorem generator_complete (total : Bool) (c : Candidate) :
    c ∈ generate total ↔ admissible total c := by
  rcases c with ⟨d,h⟩
  cases total <;> cases d <;> cases h with
  | none => decide
  | some b => cases b <;> decide

theorem generator_nodup (total : Bool) : (generate total).Nodup := by
  cases total <;> decide

theorem generator_counts : (generate true).length = 6 ∧ (generate false).length = 4 := by
  decide

theorem generator_nonempty (total : Bool) : (generate total).toFinset.Nonempty := by
  cases total <;> decide

theorem exclusive_iff (total : Bool) (w : Weights) (l : ℝ) (good : Candidate → Prop) :
    selects total w l good ↔
      ∃ a ∈ generate total, good a ∧
        ∀ b ∈ generate total, ¬ good b → score total w l a < score total w l b := by
  simpa [selects] using
    (AccentRegion.exclusive_minima_iff (generate total).toFinset (score total w l) good
      (generator_nonempty total)).symm

theorem total_fiber (c : Candidate) : compensates true c ↔ c = (true, some true) := by
  rcases c with ⟨d,h⟩
  cases d <;> cases h with
  | none => decide
  | some b => cases b <;> decide

theorem total_exact_region (w : Weights) (l : ℝ) (hw : nonnegative w) (hl : 0 ≤ l) :
    selects true w l (compensates true) ↔
      w.max + w.maxlink < w.nocoda ∧ w.maxlink < l*w.mora := by
  rw [exclusive_iff]
  simp only [total_fiber]
  simp [generate, score, coefficients, hasMora, linkedV, linkedC]
  rcases hw with ⟨hm,hn,hu,hk⟩
  have hlu := mul_nonneg hl hu
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith

theorem derived_no_compensation (c : Candidate) (hc : c ∈ generate false) :
    ¬ compensates false c := by
  rcases c with ⟨d,h⟩
  cases d <;> cases h with
  | none => simp [compensates, linkedV, hasMora]
  | some b => cases b <;> simp [generate, compensates, linkedV, hasMora] at *

theorem derived_refit_impossible (w : Weights) (l : ℝ) :
    ¬ selects false w l (compensates false) := by
  rw [exclusive_iff]
  rintro ⟨a,ha,hgood,_⟩
  exact derived_no_compensation a ha hgood

theorem derived_deletion_fiber (c : Candidate) (hc : c ∈ generate false) :
    c.1 = true ↔ c = (true, none) := by
  rcases c with ⟨d,h⟩
  cases d <;> cases h with
  | none => decide
  | some b => cases b <;> simp [generate] at *

theorem derived_deletion_region (w : Weights) (l : ℝ) (hw : nonnegative w) (hl : 0 ≤ l) :
    selects false w l (fun c => c.1 = true) ↔ w.max < w.nocoda := by
  rw [exclusive_iff]
  simp [generate, score, coefficients, hasMora, linkedV, linkedC]
  rcases hw with ⟨hm,hn,hu,hk⟩
  have hlu := mul_nonneg hl hu
  constructor
  · intro h; linarith [h.1,h.2.1,h.2.2]
  · intro h; refine ⟨?_,?_,?_⟩ <;> linarith

theorem zero_attenuation_impossible (w : Weights) (hw : nonnegative w) :
    ¬ selects true w 0 (compensates true) := by
  rw [total_exact_region w 0 hw (le_refl 0)]
  simp only [zero_mul]
  intro h
  exact (not_lt_of_ge hw.2.2.2) h.2

end CompensatoryLengthening
