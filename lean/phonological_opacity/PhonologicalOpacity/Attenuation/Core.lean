import PhonologicalOpacity.Gua.Deletion.Core
                       
namespace Attenuation
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def scores (u : Input) (i : Nat) : Nat × Nat :=
  match (counts u i).zip weights with
  | cs => ((cs.map fun (r,w) => w*r[0]!).sum, (cs.map fun (r,w) => w*r[1]!).sum)

def oldScore (u : Input) (i : Nat) : Nat := (scores u i).1

def newScore (u : Input) (i : Nat) : Nat := (scores u i).2

                       
noncomputable def pressure (u : Input) (lam : ℚ) (i : Nat) : ℚ :=
  (oldScore u i : ℚ) + lam * (newScore u i : ℚ)

theorem sum_split (l : List (List Nat × Nat)) :
    (l.map fun (r,w) => w*(8*r[0]!+r[1]!)).sum
      = 8*(l.map fun (r,w) => w*r[0]!).sum + (l.map fun (r,w) => w*r[1]!).sum := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨r, w⟩ := p
      simp only [List.map_cons, List.sum_cons, ih]
      ring

theorem score8_split (u : Input) (i : Nat) :
    score8 u 0 i = 8 * oldScore u i + newScore u i := by
  unfold score8 oldScore newScore scores
  simpa using sum_split ((counts u i).zip weights)

theorem pressure_eighth (u : Input) (i : Nat) :
    pressure u (1/8) i = (score8 u 0 i : ℚ) / 8 := by
  rw [score8_split]; unfold pressure; push_cast; ring

def checkRow (u : Input) (og ng i : Nat) : Bool :=
  match scores u i with
  | (o, n) => og < o && 4*og + ng ≤ 4*o + n

def checkAll (u : Input) (goal og ng : Nat) : Bool :=
  (carrier u).all fun i => i == goal || checkRow u og ng i

def checkBlock (u : Input) (goal og ng b : Nat) : Bool :=
  (List.range 169).all fun j => 169*b+j == goal || checkRow u og ng (169*b+j)

theorem assemble {u : Input} {goal og ng n : Nat}
    (hn : 13^u.focal.length = 169*n)
    (h : ∀ b < n, checkBlock u goal og ng b = true) : checkAll u goal og ng = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 169*n := by simpa [carrier,hn] using hi
  have hb : i/169 < n := by omega
  have hj : i%169 < 169 := Nat.mod_lt i (by decide)
  have hx := List.all_eq_true.mp (h (i/169) hb) (i%169) (List.mem_range.mpr hj)
  have he : 169*(i/169)+i%169=i := by omega
  simpa only [he] using hx

theorem row_facts {u : Input} {goal og ng i : Nat} (hc : checkAll u goal og ng = true)
    (hg : scores u goal = (og, ng))
    (hi : i ∈ carrier u) (hne : i ≠ goal) :
    oldScore u goal < oldScore u i ∧
      4*oldScore u goal + newScore u goal ≤ 4*oldScore u i + newScore u i := by
  have hx := List.all_eq_true.mp hc i hi
  have hne' : (i == goal) = false := by simpa using hne
  simp only [hne', Bool.false_or, checkRow] at hx
  unfold oldScore newScore
  rw [hg]
  revert hx
  cases scores u i with
  | mk o n => simp

theorem unique_min_on_interval {u : Input} {goal og ng : Nat} (hc : checkAll u goal og ng = true)
    (hg : scores u goal = (og, ng)) (lam : ℚ) (h0 : 0 ≤ lam) (h4 : lam < 1/4) :
    ∀ i ∈ carrier u, i ≠ goal → pressure u lam goal < pressure u lam i := by
  intro i hi hne
  obtain ⟨hold, hquarter⟩ := row_facts hc hg hi hne
  unfold pressure
  have hold' : (oldScore u goal : ℚ) < oldScore u i := by exact_mod_cast hold
  have hq' : (4*oldScore u goal + newScore u goal : ℚ)
      ≤ 4*oldScore u i + newScore u i := by exact_mod_cast hquarter
  by_cases hle : (newScore u goal : ℚ) ≤ newScore u i
  · have : (0:ℚ) ≤ lam * ((newScore u i : ℚ) - newScore u goal) :=
      mul_nonneg h0 (by linarith)
    nlinarith
  ·
    push Not at hle
    have hneg : ((newScore u i : ℚ) - newScore u goal) < 0 := by linarith
    have hmul : (1/4) * ((newScore u i : ℚ) - newScore u goal)
        < lam * ((newScore u i : ℚ) - newScore u goal) :=
      mul_lt_mul_of_neg_right h4 hneg
    nlinarith

theorem unique_min_all_lambda {u : Input} {goal og : Nat} (hc : checkAll u goal og 0 = true)
    (hg : scores u goal = (og, 0)) (lam : ℚ) (h0 : 0 ≤ lam) :
    ∀ i ∈ carrier u, i ≠ goal → pressure u lam goal < pressure u lam i := by
  intro i hi hne
  obtain ⟨hold, _⟩ := row_facts hc hg hi hne
  have hzero : newScore u goal = 0 := by unfold newScore; rw [hg]
  unfold pressure
  rw [hzero]
  have hold' : (oldScore u goal : ℚ) < oldScore u i := by exact_mod_cast hold
  have : (0:ℚ) ≤ lam * (newScore u i : ℚ) := by positivity
  push_cast; linarith

theorem tie_at_quarter {u : Input} {goal rival : Nat}
    (h : oldScore u rival = oldScore u goal + 1 ∧ newScore u goal = newScore u rival + 4) :
    pressure u (1/4) rival = pressure u (1/4) goal := by
  obtain ⟨h1, h2⟩ := h
  unfold pressure
  rw [h1, h2]; push_cast; ring

theorem rival_wins_above_quarter {u : Input} {goal rival : Nat}
    (h : oldScore u rival = oldScore u goal + 1 ∧ newScore u goal = newScore u rival + 4)
    (lam : ℚ) (hl : 1/4 < lam) :
    pressure u lam rival < pressure u lam goal := by
  obtain ⟨h1, h2⟩ := h
  unfold pressure
  rw [h1, h2]; push_cast; nlinarith

end Attenuation
