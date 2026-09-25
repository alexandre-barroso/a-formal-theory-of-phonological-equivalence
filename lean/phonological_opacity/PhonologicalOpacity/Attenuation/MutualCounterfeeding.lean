import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace MutualCounterfeedingRegion
structure Weights where
  h : ℝ
  s : ℝ
  mh : ℝ
  ms : ℝ

def Nonnegative (w : Weights) : Prop := 0 ≤ w.h ∧ 0 ≤ w.s ∧ 0 ≤ w.mh ∧ 0 ≤ w.ms

def Selects (carryLeft : Bool) (l : ℝ) (w : Weights) : Prop :=
  w.mh+l*w.s < w.h ∧
  w.mh+l*w.s < w.ms+w.h ∧
  w.mh+l*w.s < w.mh+w.ms ∧
  w.ms+l*w.h < w.s ∧
  w.ms+l*w.h < w.mh+(if carryLeft then 0 else w.s) ∧
  w.ms+l*w.h < w.mh+w.ms

def Reduced (carryLeft : Bool) (l : ℝ) (w : Weights) : Prop :=
  l*w.s < w.ms ∧ w.mh+l*w.s < w.h ∧
  l*w.h < w.mh ∧ w.ms+l*w.h < w.s ∧
  (carryLeft = true → w.ms+l*w.h < w.mh)

theorem reduction (b : Bool) (l : ℝ) (w : Weights) (hw : Nonnegative w) :
    Selects b l w ↔ Reduced b l w := by
  rcases hw with ⟨hh,hs,hmh,hms⟩
  cases b
  · simp only [Selects, Reduced, Bool.false_eq_true, ↓reduceIte, false_implies, and_true]
    constructor
    · rintro ⟨h1,h2,h3,h4,h5,h6⟩
      exact ⟨by linarith, h1, by linarith, h4⟩
    · rintro ⟨h1,h2,h3,h4⟩
      exact ⟨h2, by linarith, by linarith, h4, by linarith, by linarith⟩
  · simp only [Selects, Reduced, ↓reduceIte, true_implies, add_zero]
    constructor
    · rintro ⟨h1,h2,h3,h4,h5,h6⟩
      exact ⟨by linarith, h1, by linarith, h4, h5⟩
    · rintro ⟨h1,h2,h3,h4,h5⟩
      exact ⟨h2, by linarith, by linarith, h4, h5, by linarith⟩

def q (l : ℝ) : ℝ := 1-2*l-l^2
noncomputable def witness (b : Bool) (l : ℝ) : Weights :=
  if b then ⟨1+l,1,(3+2*l+l^2)/4,(1-l^2)/2⟩ else ⟨1,1,1/2,1/2⟩

theorem necessary_uncarried (l : ℝ) (hl : 0 ≤ l) (w : Weights)
    (hw : Nonnegative w) (h : Selects false l w) : l < 1/2 := by
  have hr := (reduction false l w hw).1 h
  rcases hw with ⟨hh,hs,hmh,hms⟩
  rcases hr with ⟨h1,h2,h3,h4,h5⟩
  by_contra hn
  have hhalf : 1/2 ≤ l := le_of_not_gt hn
  have hp := mul_nonneg (show 0 ≤ 2*l-1 by linarith) (add_nonneg hh hs)
  nlinarith

theorem necessary_carried (l : ℝ) (hl : 0 ≤ l) (w : Weights)
    (hw : Nonnegative w) (h : Selects true l w) : 0 < q l := by
  have hr := (reduction true l w hw).1 h
  rcases hw with ⟨hh,hs,hmh,hms⟩
  rcases hr with ⟨h1,h2,h3,h4,h5⟩
  have hc := h5 rfl
  have hspos : 0 < w.s := by nlinarith [mul_nonneg hl hh]
  have hA : 0 < (1-l)*w.h-2*l*w.s := by nlinarith
  have hB : 0 < (1-l)*w.s-l*w.h := by nlinarith
  have hlt : l < 1 := by
    by_contra hn
    have hge : 1 ≤ l := le_of_not_gt hn
    nlinarith [mul_nonneg (show 0 ≤ l-1 by linarith) hs, mul_nonneg hl hh]
  have hprod : 0 < q l*w.s := by
    dsimp [q]
    nlinarith [mul_nonneg hl (le_of_lt hA), mul_pos (show 0 < 1-l by linarith) hB]
  by_contra hn
  have hq : q l ≤ 0 := le_of_not_gt hn
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hq hs)) hprod

theorem witness_uncarried (l : ℝ) (hl : 0 ≤ l) (hu : l < 1/2) :
    Nonnegative (witness false l) ∧ Selects false l (witness false l) := by
  dsimp [Nonnegative, witness, Selects]
  constructor
  · norm_num
  · exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem witness_carried (l : ℝ) (hl : 0 ≤ l) (hq : 0 < q l) :
    Nonnegative (witness true l) ∧ Selects true l (witness true l) := by
  dsimp [q] at hq
  have hsq := sq_nonneg l
  have hn : Nonnegative (witness true l) := by
    dsimp [Nonnegative, witness]
    exact ⟨by linarith, by norm_num, by nlinarith, by nlinarith⟩
  refine ⟨hn, (reduction true l _ hn).2 ?_⟩
  dsimp [Reduced, witness]
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, fun _ => by nlinarith⟩

theorem q_iff (l : ℝ) (hl : 0 ≤ l) : 0 < q l ↔ l < Real.sqrt 2-1 := by
  have hs := Real.sqrt_nonneg (2:ℝ)
  have he : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [q]
  constructor
  · intro h
    by_contra hn
    have ht : Real.sqrt 2 ≤ l+1 := by linarith
    nlinarith [sq_nonneg (l+1-Real.sqrt 2)]
  · intro h
    have hdiff : 0 < Real.sqrt 2-(l+1) := by linarith
    have hsum : 0 < Real.sqrt 2+(l+1) := by linarith
    nlinarith [mul_pos hdiff hsum]

theorem exact_uncarried (l : ℝ) (hl : 0 ≤ l) :
    (∃ w, Nonnegative w ∧ Selects false l w) ↔ l < 1/2 := by
  constructor
  · rintro ⟨w,hw,h⟩; exact necessary_uncarried l hl w hw h
  · intro h; exact ⟨witness false l,witness_uncarried l hl h⟩

theorem exact_carried (l : ℝ) (hl : 0 ≤ l) :
    (∃ w, Nonnegative w ∧ Selects true l w) ↔ l < Real.sqrt 2-1 := by
  constructor
  · rintro ⟨w,hw,h⟩; exact (q_iff l hl).1 (necessary_carried l hl w hw h)
  · intro h; exact ⟨witness true l,witness_carried l hl ((q_iff l hl).2 h)⟩

theorem scalar_no_go (S : Set ℝ) (l : ℝ) (hS : l ∈ S) (hl : 0 ≤ l) (hu : l < 1/2) :
    ∃ t ∈ S, ∃ w, Nonnegative w ∧ Selects false t w := by
  exact ⟨l,hS,witness false l,witness_uncarried l hl hu⟩
end MutualCounterfeedingRegion

namespace MutualCounterfeedingRegion
abbrev State := List (Option Char)
abbrev Mode := Bool × Bool

def isC (x : Option Char) : Bool := x.any (fun c => c ∈ "ghrmpt".toList)
def isV (x : Option Char) : Bool := x.any (fun c => c ∈ "a@ue".toList)
def left (s : State) (i : Nat) : List Nat :=
  ((List.range s.length).filter (fun j => j < i && s[j]!.isSome)).reverse

def right (s : State) (i : Nat) : List Nat :=
  (List.range s.length).filter (fun j => i < j && s[j]!.isSome)

def nthPhone (s : State) (ns : List Nat) (k : Nat) : Option Char :=
  (ns[k]?).bind fun j => s[j]!

def reader (s : State) (i : Nat) (syn : Bool) (m : Mode) : Bool × Bool :=
  let ls := left s i
  let rs := right s i
  let lc := if syn then isC (nthPhone s ls 0) && isV (nthPhone s ls 1) else true
  let rc := isC (nthPhone s rs 0) && (!syn || isV (nthPhone s rs 1))
  let target := if syn then '@' else 'h'
  (s[i]! == some target && lc && rc,
    s[i]!.isSome && (!m.1 || lc) && (!m.2 || rc))

def ruleCoefficients (original s : State) (syn : Bool) (m : Mode) : ℕ × ℕ :=
  let terms := (List.range original.length).map fun i =>
    let cur := reader s i syn m
    let old := reader original i syn m
    (if cur.2 && old.1 && old.2 then 1 else 0,
     if cur.2 && !(old.1 && old.2) && cur.1 then 1 else 0)
  ((terms.map Prod.fst).sum,(terms.map Prod.snd).sum)

structure Row where
  ho : ℕ
  hn : ℕ
  ds : ℕ
  dh : ℕ
  so : ℕ
  sn : ℕ
  deriving DecidableEq, Repr

def coefficients (original s : State) (mh ms : Mode) : Row :=
  let h := ruleCoefficients original s false mh
  let v := ruleCoefficients original s true ms
  let deleted := fun c => ((List.range original.length).filter
    (fun i => original[i]! == some c && s[i]! == none)).length
  ⟨h.1,h.2,deleted '@',deleted 'h',v.1,v.2⟩

noncomputable def rowPressure (r : Row) (w : Weights) (l : ℝ) : ℝ :=
  w.h*(r.ho+l*r.hn)+w.ms*r.ds+w.mh*r.dh+w.s*(r.so+l*r.sn)

abbrev Poly := Int × Int × Int
noncomputable def evalPoly (p : Poly) (l : ℝ) : ℝ := p.1+p.2.1*l+p.2.2*l^2

def polynomial (r : Row) (carried : Bool) : Poly :=
  let h : Int := r.ho; let hn : Int := r.hn
  let ds : Int := r.ds; let dh : Int := r.dh
  let s : Int := r.so; let sn : Int := r.sn
  if carried then (4*h+2*ds+3*dh+4*s,4*h+4*hn+2*dh+4*sn,4*hn-2*ds+dh)
  else (4*h+2*ds+2*dh+4*s,4*hn+4*sn,0)

def subtract (p q : Poly) : Poly := (p.1-q.1,p.2.1-q.2.1,p.2.2-q.2.2)

theorem polynomial_correct (r : Row) (b : Bool) (l : ℝ) :
    evalPoly (polynomial r b) l = 4*rowPressure r (witness b l) l := by
  cases b <;> simp [evalPoly,polynomial,rowPressure,witness] <;> push_cast <;> ring

theorem subtract_correct (p q : Poly) (l : ℝ) :
    evalPoly (subtract p q) l = evalPoly p l-evalPoly q l := by
  simp [evalPoly,subtract]; ring

def admissiblePolynomials (b : Bool) : List Poly :=
  if b then [(1,-2,-1),(1,2,-1),(2,-4,-2),(2,0,-2),(2,0,2),(2,4,2),
    (3,-2,-3),(3,2,1),(4,4,0),(5,2,-1),(7,2,-3)]
  else [(2,-4,0),(2,0,0),(2,4,0),(4,-4,0),(4,0,0),(4,4,0),(6,0,0)]

theorem admissible_positive (b : Bool) (l : ℝ) (hl : 0 ≤ l)
    (hb : if b then 0 < q l else l < 1/2) (p : Poly)
    (hp : p ∈ admissiblePolynomials b) : 0 < evalPoly p l := by
  cases b
  · simp only [admissiblePolynomials, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num only [evalPoly, Int.cast_ofNat, Int.cast_neg] <;> dsimp at hb <;> linarith
  · simp only [admissiblePolynomials, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num only [evalPoly, Int.cast_ofNat, Int.cast_neg] <;> dsimp [q] at hb <;> nlinarith [sq_nonneg l]

def initial (s : String) : State := s.toList.map some

def generate : State → List State
  | [] => [[]]
  | c::cs => (if c == some 'h' || c == some '@' then [c,none] else [c]).flatMap
    fun x => (generate cs).map (x :: ·)

def surface (s : State) : String := String.ofList (s.filterMap id)

def paradigm : List (String × String) :=
  [("gahe","gahe"),("gaht","gat"),("mae","mae"),("mat","mat"),
  ("mar@mu","marmu"),("ah@pt","ah@pt"),("ah@pr@mu","ah@pr@mu"),
  ("gahr@mu","gar@mu"),("ah@pe","ahpe")]

def target (p : String × String) : State :=
  ((generate (initial p.1)).find? (fun c => surface c == p.2)).getD []

def margin (mh ms : Mode) (p : String × String) (c : State) : Poly :=
  subtract (polynomial (coefficients (initial p.1) c mh ms) ms.1)
    (polynomial (coefficients (initial p.1) (target p) mh ms) ms.1)

def certificate (mh ms : Mode) : Bool := paradigm.all fun p =>
  (generate (initial p.1)).all fun c => surface c == p.2 || margin mh ms p c ∈ admissiblePolynomials ms.1

theorem all_certificates (mh ms : Mode) : certificate mh ms = true := by
  rcases mh with ⟨hl,hr⟩;rcases ms with ⟨sl,sr⟩
  cases hl <;> cases hr <;> cases sl <;> cases sr <;> decide +kernel

theorem target_fibers : ∀ p ∈ paradigm,
    target p ∈ generate (initial p.1) ∧
    ∀ c ∈ generate (initial p.1), surface c = p.2 ↔ c = target p := by decide +kernel

theorem complete_separation (mh ms : Mode) (l : ℝ) (hl : 0 ≤ l)
    (hb : if ms.1 then 0 < q l else l < 1/2) :
    ∀ p ∈ paradigm, ∀ c ∈ generate (initial p.1), surface c ≠ p.2 →
    rowPressure (coefficients (initial p.1) (target p) mh ms) (witness ms.1 l) l <
    rowPressure (coefficients (initial p.1) c mh ms) (witness ms.1 l) l := by
  intro p hp c hc hwrong
  have h1 := List.all_eq_true.mp (all_certificates mh ms) p hp
  have h2 := List.all_eq_true.mp h1 c hc
  have hmem : margin mh ms p c ∈ admissiblePolynomials ms.1 := by
    simpa [hwrong] using h2
  have hpos := admissible_positive ms.1 l hl hb _ hmem
  rw [margin,subtract_correct,polynomial_correct,polynomial_correct] at hpos
  linarith
end MutualCounterfeedingRegion

namespace MutualCounterfeedingRegion
noncomputable def pressure (mh ms : Mode) (p : String × String) (w : Weights) (l : ℝ) (c : State) :=
  rowPressure (coefficients (initial p.1) c mh ms) w l

def FullSelection (mh ms : Mode) (l : ℝ) (w : Weights) : Prop :=
  ∀ p ∈ paradigm,
    (∃ g ∈ generate (initial p.1), ∀ c ∈ generate (initial p.1), pressure mh ms p w l g ≤ pressure mh ms p w l c) ∧
    (∀ g ∈ generate (initial p.1),
      (∀ c ∈ generate (initial p.1), pressure mh ms p w l g ≤ pressure mh ms p w l c) → surface g = p.2)

def FullSeparation (mh ms : Mode) (l : ℝ) (w : Weights) : Prop :=
  ∀ p ∈ paradigm, ∀ c ∈ generate (initial p.1), surface c ≠ p.2 →
    pressure mh ms p w l (target p) < pressure mh ms p w l c

theorem full_equivalence (mh ms : Mode) (l : ℝ) (w : Weights) :
    FullSelection mh ms l w ↔ FullSeparation mh ms l w := by
  constructor
  · intro h p hp c hc hwrong
    obtain ⟨⟨g,hg,hmin⟩,hcorrect⟩ := h p hp
    have he := ((target_fibers p hp).2 g hg).1 (hcorrect g hg hmin)
    subst g
    by_contra hn
    have hcm : ∀ d ∈ generate (initial p.1), pressure mh ms p w l c ≤ pressure mh ms p w l d := by
      intro d hd
      exact le_trans (le_of_not_gt hn) (hmin d hd)
    exact hwrong (hcorrect c hc hcm)
  · intro h p hp
    have ht := (target_fibers p hp).1
    have hn : ((generate (initial p.1)).toFinset).Nonempty := ⟨target p, by simpa using ht⟩
    obtain ⟨g,hg,hmin⟩ := ((generate (initial p.1)).toFinset).exists_min_image (pressure mh ms p w l) hn
    have hg' : g ∈ generate (initial p.1) := by simpa using hg
    have hmin' : ∀ c ∈ generate (initial p.1), pressure mh ms p w l g ≤ pressure mh ms p w l c := by
      intro c hc;exact hmin c (by simpa using hc)
    refine ⟨⟨g,hg',hmin'⟩,?_⟩
    intro c hc hcm
    by_contra hw
    exact (not_lt_of_ge (hcm (target p) ht)) (h p hp c hc hw)

theorem full_witness (mh ms : Mode) (l : ℝ) (hl : 0 ≤ l)
    (hb : if ms.1 then 0 < q l else l < 1/2) : FullSelection mh ms l (witness ms.1 l) := by
  apply (full_equivalence mh ms l _).2
  exact complete_separation mh ms l hl hb

def masked (s : String) : State := s.toList.map fun c => if c = '-' then none else some c

def x : String × String := ("gahr@mu","gar@mu")
def y : String × String := ("ah@pe","ahpe")

theorem critical_coefficients (mh ms : Mode) :
  target x = masked "ga-r@mu" ∧ target y = masked "ah-pe" ∧
  coefficients (initial x.1) (target x) mh ms = ⟨0,0,0,1,0,1⟩ ∧
  coefficients (initial x.1) (initial x.1) mh ms = ⟨1,0,0,0,0,0⟩ ∧
  coefficients (initial x.1) (masked "gahr-mu") mh ms = ⟨1,0,1,0,0,0⟩ ∧
  coefficients (initial x.1) (masked "ga-r-mu") mh ms = ⟨0,0,1,1,0,0⟩ ∧
  coefficients (initial y.1) (target y) mh ms = ⟨0,1,1,0,0,0⟩ ∧
  coefficients (initial y.1) (initial y.1) mh ms = ⟨0,0,0,0,1,0⟩ ∧
  coefficients (initial y.1) (masked "a-@pe") mh ms = ⟨0,0,0,1,if ms.1 then 0 else 1,0⟩ ∧
  coefficients (initial y.1) (masked "a--pe") mh ms = ⟨0,0,1,1,0,0⟩ := by
  rcases mh with ⟨hl,hr⟩;rcases ms with ⟨sl,sr⟩
  cases hl <;> cases hr <;> cases sl <;> cases sr <;> decide +kernel

theorem full_implies_critical (mh ms : Mode) (l : ℝ) (w : Weights)
    (h : FullSelection mh ms l w) : Selects ms.1 l w := by
  have hs := (full_equivalence mh ms l w).1 h
  rcases critical_coefficients mh ms with ⟨_,_,cxg,cxn,cxs,cxb,cyg,cyn,cyh,cyb⟩
  have h1 := hs x (by decide) (initial x.1) (by decide +kernel) (by decide)
  have h2 := hs x (by decide) (masked "gahr-mu") (by decide +kernel) (by decide)
  have h3 := hs x (by decide) (masked "ga-r-mu") (by decide +kernel) (by decide)
  have h4 := hs y (by decide) (initial y.1) (by decide +kernel) (by decide)
  have h5 := hs y (by decide) (masked "a-@pe") (by decide +kernel) (by decide)
  have h6 := hs y (by decide) (masked "a--pe") (by decide +kernel) (by decide)
  simp only [pressure,cxg,cxn,cxs,cxb,cyg,cyn,cyh,cyb,rowPressure] at h1 h2 h3 h4 h5 h6
  cases hleft : ms.1 <;> simp [Selects,hleft] at * <;> exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem full_exact_region (mh ms : Mode) (l : ℝ) (hl : 0 ≤ l) :
    (∃ w, Nonnegative w ∧ FullSelection mh ms l w) ↔
      (if ms.1 then l < Real.sqrt 2-1 else l < 1/2) := by
  constructor
  · rintro ⟨w,hw,h⟩
    have hc := full_implies_critical mh ms l w h
    cases hleft : ms.1
    · simp only [hleft,Bool.false_eq_true,↓reduceIte];exact necessary_uncarried l hl w hw (by simpa [hleft] using hc)
    · simp only [hleft,Bool.false_eq_true,↓reduceIte];exact (q_iff l hl).1 (necessary_carried l hl w hw (by simpa [hleft] using hc))
  · intro h
    have hb : if ms.1 then 0 < q l else l < 1/2 := by
      cases hleft : ms.1 <;> simp only [hleft,Bool.false_eq_true,↓reduceIte] at *
      · exact h
      · exact (q_iff l hl).2 h
    have hw : Nonnegative (witness ms.1 l) := by
      cases hleft : ms.1 <;> simp only [hleft,Bool.false_eq_true,↓reduceIte] at hb ⊢
      · exact (witness_uncarried l hl hb).1
      · exact (witness_carried l hl hb).1
    exact ⟨witness ms.1 l,hw,full_witness mh ms l hl hb⟩
end MutualCounterfeedingRegion
