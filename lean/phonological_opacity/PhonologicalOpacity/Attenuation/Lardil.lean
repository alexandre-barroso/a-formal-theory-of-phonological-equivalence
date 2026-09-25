import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace LardilRegion
abbrev State := List (Option String)
abbrev Form := List String
abbrev Mode := Bool × Bool
structure Weights where
  a : ℝ
  k : ℝ
  mv : ℝ
  mc : ℝ
def Nonnegative (w : Weights) : Prop := 0 ≤ w.a ∧ 0 ≤ w.k ∧ 0 ≤ w.mv ∧ 0 ≤ w.mc
def isV (x : Option String) : Bool := x.any (fun c => c ∈ ["a","i","u"])
def isK (x : Option String) : Bool := x.any (fun c => c ∈ ["w","th","ŋ"])
def previousV (s : State) (i : Nat) : List Nat :=
  ((List.range s.length).filter (fun j => j < i && isV s[j]!)).reverse
def nextPresent (s : State) (i : Nat) : Option Nat :=
  (List.range s.length).find? (fun j => i < j && s[j]!.isSome)
def reader (s : State) (i : Nat) (apo : Bool) (m : Mode) : Bool × Bool × List (Option Nat) :=
  let p := (previousV s i)[1]?
  let n := nextPresent s i
  let lc := !apo || p.isSome
  let rc := n.isNone
  ( (if apo then isV s[i]! else isK s[i]!) && lc && rc,
    s[i]!.isSome && (!m.1 || lc) && (!m.2 || rc),
    (if m.1 && apo then [p] else []) ++ (if m.2 then [n] else []) ++ [some i])
def ruleCoefficients (original s : State) (apo : Bool) (m : Mode) (sub : Bool) : ℕ × ℕ :=
  let before := (List.range original.length).map fun i => reader original i apo m
  let marked := (before.filter fun r => r.1 && r.2.1).map fun r => r.2.2
  let terms := (List.range original.length).map fun i =>
    let cur := reader s i apo m
    let old := before[i]!
    let retained := if sub then cur.2.2 ∈ marked else old.1 && old.2.1
    (if cur.2.1 && retained then 1 else 0,
     if cur.2.1 && !retained && cur.1 then 1 else 0)
  ((terms.map Prod.fst).sum,(terms.map Prod.snd).sum)
structure Row where
  ao : ℕ
  an : ℕ
  ko : ℕ
  kn : ℕ
  dv : ℕ
  dk : ℕ
  deriving DecidableEq, Repr
def coefficients (original s : State) (ma mk : Mode) (sub : Bool) : Row :=
  let a := ruleCoefficients original s true ma sub
  let k := ruleCoefficients original s false mk sub
  let deleted := fun cls => ((List.range original.length).filter
    (fun i => cls original[i]! && s[i]!.isNone)).length
  ⟨a.1,a.2,k.1,k.2,deleted isV,deleted isK⟩
noncomputable def rowPressure (r : Row) (w : Weights) (l : ℝ) : ℝ :=
  w.a*(r.ao+l*r.an)+w.k*(r.ko+l*r.kn)+w.mv*r.dv+w.mc*r.dk
noncomputable def witness (l : ℝ) : Weights := ⟨1,2,1/2,l*(1-2*l)/2⟩
abbrev Poly := Int × Int × Int
noncomputable def evalPoly (p : Poly) (l : ℝ) : ℝ := p.1+p.2.1*l+p.2.2*l^2
def polynomial (r : Row) : Poly :=
  (2*(r.ao:Int)+4*(r.ko:Int)+(r.dv:Int),2*(r.an:Int)+4*(r.kn:Int)+(r.dk:Int),-2*(r.dk:Int))
def subtract (p q : Poly) : Poly := (p.1-q.1,p.2.1-q.2.1,p.2.2-q.2.2)
theorem polynomial_correct (r : Row) (l : ℝ) :
    evalPoly (polynomial r) l = 2*rowPressure r (witness l) l := by
  simp [evalPoly,polynomial,rowPressure,witness];ring
theorem subtract_correct (p q : Poly) (l : ℝ) :
    evalPoly (subtract p q) l = evalPoly p l-evalPoly q l := by
  simp [evalPoly,subtract];ring
def Admissible (p : Poly) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ 4*p.1+p.2.1 ∧ 0 ≤ 4*p.1+2*p.2.1+p.2.2 ∧
  (0 < p.1 ∨ 0 < 4*p.1+p.2.1 ∨ 0 < 4*p.1+2*p.2.1+p.2.2)
instance (p : Poly) : Decidable (Admissible p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
theorem admissible_positive (p : Poly) (l : ℝ) (hl : 0 < l) (hu : l < 1/2)
    (hp : Admissible p) : 0 < evalPoly p l := by
  rcases hp with ⟨hA,hB,hC,hpos⟩
  have ha : 0 ≤ (p.1:ℝ) := by exact_mod_cast hA
  have hb : 0 ≤ 4*(p.1:ℝ)+(p.2.1:ℝ) := by exact_mod_cast hB
  have hc : 0 ≤ 4*(p.1:ℝ)+2*(p.2.1:ℝ)+(p.2.2:ℝ) := by exact_mod_cast hC
  have hx : 0 < 1-2*l := by linarith
  have hxx := sq_pos_of_pos hx
  have hll := sq_pos_of_pos hl
  have hxl := mul_pos hl hx
  have tA := mul_nonneg ha (le_of_lt hxx)
  have tB := mul_nonneg hb (le_of_lt hxl)
  have tC := mul_nonneg hc (le_of_lt hll)
  have hid : evalPoly p l = (p.1:ℝ)*(1-2*l)^2+
      (4*(p.1:ℝ)+(p.2.1:ℝ))*(l*(1-2*l))+
      (4*(p.1:ℝ)+2*(p.2.1:ℝ)+(p.2.2:ℝ))*l^2 := by dsimp [evalPoly];ring
  rw [hid]
  rcases hpos with h|h|h
  · have h' : 0 < (p.1:ℝ) := by exact_mod_cast h
    linarith [mul_pos h' hxx]
  · have h' : 0 < 4*(p.1:ℝ)+(p.2.1:ℝ) := by exact_mod_cast h
    linarith [mul_pos h' hxl]
  · have h' : 0 < 4*(p.1:ℝ)+2*(p.2.1:ℝ)+(p.2.2:ℝ) := by exact_mod_cast h
    linarith [mul_pos h' hll]
def initial (s : Form) : State := s.map some
def generate : State → List State
  | [] => [[]]
  | c::cs => (if isV c || isK c then [c,none] else [c]).flatMap
    fun x => (generate cs).map (x :: ·)
def surface (s : State) : Form := s.filterMap id
def wi : Form × Form := (["w","i","w","a","l","a"],["w","i","w","a","l"])
def thu : Form × Form := (["th","u","r","a","r","a","ŋ"],["th","u","r","a","r","a"])
def nga : Form × Form := (["ŋ","a","w","u","ŋ","a","w","u"],["ŋ","a","w","u","ŋ","a"])
def paradigm : List (Form × Form) := [wi,thu,nga]
def target (p : Form × Form) : State :=
  ((generate (initial p.1)).find? (fun c => surface c == p.2)).getD []
def margin (ma mk : Mode) (sub : Bool) (p : Form × Form) (c : State) : Poly :=
  subtract (polynomial (coefficients (initial p.1) c ma mk sub))
    (polynomial (coefficients (initial p.1) (target p) ma mk sub))
def certificate (ar : Bool) (mk : Mode) (sub : Bool) : Bool := paradigm.all fun p =>
  (generate (initial p.1)).all fun c => surface c == p.2 || decide (Admissible (margin (false,ar) mk sub p c))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_certificates (ar : Bool) (mk : Mode) (sub : Bool) : certificate ar mk sub = true := by
  rcases mk with ⟨kl,kr⟩
  cases ar <;> cases kl <;> cases kr <;> cases sub <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem target_fibers : ∀ p ∈ paradigm,
    target p ∈ generate (initial p.1) ∧
    ∀ c ∈ generate (initial p.1), surface c = p.2 ↔ c = target p := by decide +kernel
noncomputable def pressure (ma mk : Mode) (sub : Bool) (p : Form × Form) (w : Weights) (l : ℝ) (c : State) :=
  rowPressure (coefficients (initial p.1) c ma mk sub) w l
def FullSelection (ma mk : Mode) (sub : Bool) (l : ℝ) (w : Weights) : Prop :=
  ∀ p ∈ paradigm,
    (∃ g ∈ generate (initial p.1), ∀ c ∈ generate (initial p.1), pressure ma mk sub p w l g ≤ pressure ma mk sub p w l c) ∧
    (∀ g ∈ generate (initial p.1),
      (∀ c ∈ generate (initial p.1), pressure ma mk sub p w l g ≤ pressure ma mk sub p w l c) → surface g = p.2)
def FullSeparation (ma mk : Mode) (sub : Bool) (l : ℝ) (w : Weights) : Prop :=
  ∀ p ∈ paradigm, ∀ c ∈ generate (initial p.1), surface c ≠ p.2 →
    pressure ma mk sub p w l (target p) < pressure ma mk sub p w l c
theorem full_equivalence (ma mk : Mode) (sub : Bool) (l : ℝ) (w : Weights) :
    FullSelection ma mk sub l w ↔ FullSeparation ma mk sub l w := by
  constructor
  · intro h p hp c hc hwrong
    obtain ⟨⟨g,hg,hmin⟩,hcorrect⟩ := h p hp
    have he := ((target_fibers p hp).2 g hg).1 (hcorrect g hg hmin)
    subst g
    by_contra hn
    have hcm : ∀ d ∈ generate (initial p.1), pressure ma mk sub p w l c ≤ pressure ma mk sub p w l d := by
      intro d hd;exact le_trans (le_of_not_gt hn) (hmin d hd)
    exact hwrong (hcorrect c hc hcm)
  · intro h p hp
    have ht := (target_fibers p hp).1
    have hn : ((generate (initial p.1)).toFinset).Nonempty := ⟨target p, by simpa using ht⟩
    obtain ⟨g,hg,hmin⟩ := ((generate (initial p.1)).toFinset).exists_min_image (pressure ma mk sub p w l) hn
    have hg' : g ∈ generate (initial p.1) := by simpa using hg
    have hmin' : ∀ c ∈ generate (initial p.1), pressure ma mk sub p w l g ≤ pressure ma mk sub p w l c := by
      intro c hc;exact hmin c (by simpa using hc)
    refine ⟨⟨g,hg',hmin'⟩,?_⟩
    intro c hc hcm
    by_contra hw
    exact (not_lt_of_ge (hcm (target p) ht)) (h p hp c hc hw)
theorem full_witness (ar : Bool) (mk : Mode) (sub : Bool) (l : ℝ) (hl : 0 < l) (hu : l < 1/2) :
    Nonnegative (witness l) ∧ FullSelection (false,ar) mk sub l (witness l) := by
  constructor
  · dsimp [Nonnegative,witness]
    refine ⟨by norm_num,by norm_num,by norm_num,?_⟩
    exact div_nonneg (mul_nonneg (le_of_lt hl) (by linarith)) (by norm_num)
  · apply (full_equivalence _ _ _ _ _).2
    intro p hp c hc hwrong
    have h1 := List.all_eq_true.mp (all_certificates ar mk sub) p hp
    have h2 := List.all_eq_true.mp h1 c hc
    have hmem : Admissible (margin (false,ar) mk sub p c) := by simpa [hwrong] using h2
    have hpos := admissible_positive _ l hl hu hmem
    rw [margin,subtract_correct,polynomial_correct,polynomial_correct] at hpos
    dsimp [pressure];linarith
def candidate (p : Form × Form) (i : Nat) : State := (generate (initial p.1))[i]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem critical_coefficients (ar : Bool) (mk : Mode) (sub : Bool) :
    coefficients (initial nga.1) (target nga) (false,ar) mk sub = ⟨0,1,0,0,1,1⟩ ∧
    coefficients (initial nga.1) (candidate nga 0) (false,ar) mk sub = ⟨1,0,0,0,0,0⟩ ∧
    coefficients (initial nga.1) (candidate nga 1) (false,ar) mk sub = ⟨0,0,0,1,1,0⟩ ∧
    coefficients (initial thu.1) (target thu) (false,ar) mk sub = ⟨0,1,0,0,0,1⟩ ∧
    coefficients (initial thu.1) (candidate thu 3) (false,ar) mk sub = ⟨0,0,0,0,1,1⟩ := by
  rcases mk with ⟨kl,kr⟩;cases ar <;> cases kl <;> cases kr <;> cases sub <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem carried_tie (ar : Bool) (mk : Mode) (sub : Bool) :
    coefficients (initial wi.1) (target wi) (true,ar) mk sub =
      coefficients (initial wi.1) (candidate wi 2) (true,ar) mk sub := by
  rcases mk with ⟨kl,kr⟩;cases ar <;> cases kl <;> cases kr <;> cases sub <;> decide +kernel
theorem carried_impossible (ar : Bool) (mk : Mode) (sub : Bool) (l : ℝ) (w : Weights) :
    ¬ FullSelection (true,ar) mk sub l w := by
  intro h
  have hs := (full_equivalence _ _ _ _ _).1 h wi (by decide) (candidate wi 2) (by decide +kernel) (by decide +kernel)
  dsimp [pressure] at hs
  rw [carried_tie ar mk sub] at hs
  exact (lt_irrefl _) hs
theorem necessary_uncarried (ar : Bool) (mk : Mode) (sub : Bool) (l : ℝ) (hl : 0 ≤ l)
    (w : Weights) (hw : Nonnegative w) (h : FullSelection (false,ar) mk sub l w) : 0 < l ∧ l < 1/2 := by
  have hs := (full_equivalence _ _ _ _ _).1 h
  rcases critical_coefficients ar mk sub with ⟨hng,hn0,hn1,htg,ht3⟩
  have h1 := hs nga (by decide) (candidate nga 0) (by decide +kernel) (by decide +kernel)
  have h2 := hs nga (by decide) (candidate nga 1) (by decide +kernel) (by decide +kernel)
  have h3 := hs thu (by decide) (candidate thu 3) (by decide +kernel) (by decide +kernel)
  simp only [pressure,hng,hn0,hn1,htg,ht3,rowPressure] at h1 h2 h3
  norm_num at h1 h2 h3
  rcases hw with ⟨ha,hk,hmv,hmk⟩
  constructor
  · by_contra hn
    have hz : l=0 := le_antisymm (le_of_not_gt hn) hl
    subst l;norm_num at h2;linarith
  · by_contra hn
    have hh : 1/2 ≤ l := le_of_not_gt hn
    nlinarith [mul_nonneg (show 0 ≤ 2*l-1 by linarith) ha]
theorem full_exact_region (ma mk : Mode) (sub : Bool) (l : ℝ) (hl : 0 ≤ l) :
    (∃ w, Nonnegative w ∧ FullSelection ma mk sub l w) ↔ ma.1 = false ∧ 0 < l ∧ l < 1/2 := by
  rcases ma with ⟨al,ar⟩
  cases al
  · simp only [true_and]
    constructor
    · rintro ⟨w,hw,h⟩;exact necessary_uncarried ar mk sub l hl w hw h
    · rintro ⟨hlo,hhi⟩;exact ⟨witness l,full_witness ar mk sub l hlo hhi⟩
  · simp only [Bool.true_eq_false,false_and,iff_false]
    rintro ⟨w,_,h⟩;exact carried_impossible ar mk sub l w h
end LardilRegion
