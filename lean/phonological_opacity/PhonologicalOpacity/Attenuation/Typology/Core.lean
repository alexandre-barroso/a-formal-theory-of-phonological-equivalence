import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace InteractionTypology
abbrev State := List (Option String)
abbrev Form := List String
abbrev Mode := Bool × Bool
structure Rule where
  name : String
  target : String
  left : List String
  right : List String
  output : Option String
  deriving DecidableEq, Repr
structure Faith where
  name : String
  target : String
  output : Option String
  deriving DecidableEq, Repr
structure Pattern where
  alphabet : List (String × List String)
  rules : List Rule
  faith : List Faith
  names : List String
  options : List (String × List (Option String))
  observations : List (Form × String)
  deriving DecidableEq, Repr
def classes (p : Pattern) (x : Option String) : List String :=
  ((p.alphabet.find? fun a => some a.1 == x).map Prod.snd).getD []
def neighbors (s : State) (i : Nat) (left : Bool) : List Nat :=
  let js := (List.range s.length).filter fun j => (if left then j < i else i < j) && s[j]!.isSome
  if left then js.reverse else js
def context (p : Pattern) (s : State) (js : List Nat) (cs : List String) : Bool :=
  cs.zipIdx |>.all fun (c,j) =>
    if c == "#" then (js[j]?).isNone else (js[j]?).any fun k => c ∈ classes p s[k]!
def reader (p : Pattern) (s : State) (i : Nat) (r : Rule) (m : Mode) : Bool × Bool × List (Option Nat) :=
  let left := neighbors s i true
  let right := neighbors s i false
  let lc := context p s left r.left
  let rc := context p s right r.right
  let carried := (!m.1 || lc) && (!m.2 || rc)
  let pressure := s[i]!.isSome && carried && (r.output.isNone || s[i]! != r.output)
  let key := (if m.1 then (List.range r.left.length).map (left[·]?) else []) ++
    (if m.2 then (List.range r.right.length).map (right[·]?) else []) ++ [some i]
  (r.target ∈ classes p s[i]! && lc && rc,pressure,key)
abbrev Row := List (Nat × Nat)
def ruleCount (p : Pattern) (original s : State) (r : Rule) (m : Mode) (sub : Bool) : Nat × Nat :=
  let before := (List.range original.length).map fun i => reader p original i r m
  let marked := (before.filter fun x => x.1 && x.2.1).map fun x => x.2.2
  let terms := (List.range s.length).map fun i =>
    let now := reader p s i r m
    let old := before[i]!
    let retained := if sub then now.2.2 ∈ marked else old.1 && old.2.1
    (if now.2.1 && retained then 1 else 0,if now.2.1 && !retained && now.1 then 1 else 0)
  ((terms.map Prod.fst).sum,(terms.map Prod.snd).sum)
def faithCount (p : Pattern) (original s : State) (f : Faith) : Nat × Nat :=
  (((List.range original.length).filter fun i => f.target ∈ classes p original[i]! &&
    (if f.output.isNone then s[i]!.isNone else s[i]! == f.output)).length,0)
def coefficients (p : Pattern) (original s : State) (ms : List Mode) (sub : Bool) : Row :=
  p.names.map fun n => match (p.rules.zip ms).find? (fun x => x.1.name == n) with
    | some (r,m) => ruleCount p original s r m sub
    | none => match p.faith.find? (fun f => f.name == n) with
      | some f => faithCount p original s f
      | none => (0,0)
def generate (p : Pattern) : State → List State
  | [] => [[]]
  | x::xs => (((p.options.find? fun a => some a.1 == x).map Prod.snd).getD [x]).flatMap
    fun y => (generate p xs).map (y :: ·)
def surface (s : State) : String := String.join (s.filterMap id)
abbrev Candidate := String × Row
abbrev Table := String × List Candidate
def tables (p : Pattern) (ms : List Mode) (sub : Bool) : List Table :=
  p.observations.map fun (input,target) =>
    let original := input.map some
    (target,(generate p original).map fun s => (surface s,coefficients p original s ms sub))
structure Weights where
  w0 : ℝ
  w1 : ℝ
  w2 : ℝ
  w3 : ℝ
  w4 : ℝ
  w5 : ℝ
  w6 : ℝ
  w7 : ℝ
  w8 : ℝ
def values (w : Weights) : List ℝ := [w.w0,w.w1,w.w2,w.w3,w.w4,w.w5,w.w6,w.w7,w.w8]
def Nonnegative (w : Weights) : Prop :=
  0≤w.w0 ∧ 0≤w.w1 ∧ 0≤w.w2 ∧ 0≤w.w3 ∧ 0≤w.w4 ∧ 0≤w.w5 ∧ 0≤w.w6 ∧ 0≤w.w7 ∧ 0≤w.w8
noncomputable def dotNat (l : ℝ) : Row → List ℝ → ℝ
  | (a,b)::rs,v::vs => ((a:ℝ)+l*(b:ℝ))*v+dotNat l rs vs
  | _,_ => 0
noncomputable def score (row : Row) (w : Weights) (l : ℝ) : ℝ := dotNat l row (values w)
def Selection (rows : List Candidate) (goal : String) (w : Weights) (l : ℝ) : Prop :=
  (∃ g ∈ rows, ∀ c ∈ rows,score g.2 w l ≤ score c.2 w l) ∧
  (∀ g ∈ rows,(∀ c ∈ rows,score g.2 w l ≤ score c.2 w l) → g.1=goal)
def Separation (rows : List Candidate) (goal : String) (w : Weights) (l : ℝ) : Prop :=
  ∃ g ∈ rows,g.1=goal ∧ ∀ c ∈ rows,c.1≠goal → score g.2 w l < score c.2 w l
theorem selection_iff_separation (rows : List Candidate) (goal : String) (w : Weights) (l : ℝ) :
    Selection rows goal w l ↔ Separation rows goal w l := by
  constructor
  · rintro ⟨⟨g,hg,hm⟩,hc⟩
    refine ⟨g,hg,hc g hg hm,?_⟩
    intro c hcm hw
    by_contra hn
    have hmin : ∀ d∈rows,score c.2 w l ≤ score d.2 w l := by
      intro d hd;exact le_trans (le_of_not_gt hn) (hm d hd)
    exact hw (hc c hcm hmin)
  · rintro ⟨g,hg,hgood,hs⟩
    have hne : rows.toFinset.Nonempty := ⟨g,by simpa using hg⟩
    obtain ⟨m,hm,hmin⟩ := rows.toFinset.exists_min_image (fun x => score x.2 w l) hne
    have hm' : m∈rows := by simpa using hm
    have hmin' : ∀ c∈rows,score m.2 w l ≤ score c.2 w l := by intro c hc;exact hmin c (by simpa using hc)
    refine ⟨⟨m,hm',hmin'⟩,?_⟩
    intro c hc hcm
    by_contra hw
    exact (not_lt_of_ge (hcm g hg)) (hs c hc hw)
def FullSelection (p : Pattern) (ms : List Mode) (sub : Bool) (w : Weights) (l : ℝ) : Prop :=
  ∀ t∈tables p ms sub,Selection t.2 t.1 w l
def FullSeparation (ts : List Table) (w : Weights) (l : ℝ) : Prop :=
  ∀ t∈ts,Separation t.2 t.1 w l
theorem full_iff (p : Pattern) (ms : List Mode) (sub : Bool) (w : Weights) (l : ℝ) :
    FullSelection p ms sub w l ↔ FullSeparation (tables p ms sub) w l := by
  simp only [FullSelection,FullSeparation,selection_iff_separation]
abbrev Delta := List (Int × Int)
def subtract (r q : Row) : Delta := (r.zip q).map fun (a,b) => ((a.1:Int)-b.1,(a.2:Int)-b.2)
noncomputable def dotInt (l : ℝ) : Delta → List ℝ → ℝ
  | (a,b)::rs,v::vs => ((a:ℝ)+l*(b:ℝ))*v+dotInt l rs vs
  | _,_ => 0
noncomputable def evalDelta (r : Delta) (w : Weights) (l : ℝ) : ℝ := dotInt l r (values w)
theorem subtract_score (r q : Row) (ws : List ℝ) (l : ℝ) (he : r.length=q.length) :
    dotInt l (subtract r q) ws = dotNat l r ws-dotNat l q ws := by
  induction r generalizing q ws with
  | nil =>
    have hq : q=[] := List.length_eq_zero_iff.mp he.symm
    subst q;simp [subtract,dotInt,dotNat]
  | cons a rs ih =>
    cases q with
    | nil => simp at he
    | cons b qs =>
      have ht : rs.length=qs.length := by simpa using he
      cases ws with
      | nil => simp [subtract,dotInt,dotNat]
      | cons v vs =>
        simp only [subtract,List.zip_cons_cons,List.map_cons,dotInt,dotNat]
        have hh := ih qs vs ht
        simp only [subtract] at hh
        rw [hh]
        push_cast
        ring
def inputBranches (t : Table) : List (List Delta) :=
  (t.2.filter fun g => g.1==t.1).map fun g =>
    (t.2.filter fun c => c.1!=t.1).map fun c => subtract c.2 g.2
def combine : List (List (List Delta)) → List (List Delta)
  | [] => [[]]
  | x::xs => x.flatMap fun a => (combine xs).map fun b => a++b
def systems (ts : List Table) : List (List Delta) := combine (ts.map inputBranches)
def SystemHolds (ss : List (List Delta)) (w : Weights) (l : ℝ) : Prop :=
  ∃ b∈ss,∀ d∈b,0<evalDelta d w l
theorem separation_iff_input (t : Table) (w : Weights) (l : ℝ)
    (hlen : ∀a∈t.2,∀b∈t.2,a.2.length=b.2.length) :
    Separation t.2 t.1 w l ↔ SystemHolds (inputBranches t) w l := by
  constructor
  · rintro ⟨g,hg,hgood,hs⟩
    refine ⟨(t.2.filter fun c => c.1!=t.1).map (fun c => subtract c.2 g.2),?_,?_⟩
    · apply List.mem_map.mpr
      exact ⟨g,by simp [hg,hgood],rfl⟩
    · intro d hd
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
      have hmem : c∈t.2 := (List.mem_filter.mp hc).1
      have hwrong : c.1≠t.1 := by simpa using (List.mem_filter.mp hc).2
      have hdelta := subtract_score c.2 g.2 (values w) l (hlen c hmem g hg)
      have hp := hs c hmem hwrong
      dsimp [score,evalDelta] at *
      linarith
  · rintro ⟨b,hb,hs⟩
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hb
    have hmem : g∈t.2 := (List.mem_filter.mp hg).1
    have hgood : g.1=t.1 := by simpa using (List.mem_filter.mp hg).2
    refine ⟨g,hmem,hgood,?_⟩
    intro c hc hw
    have hd : subtract c.2 g.2 ∈ (t.2.filter fun c => c.1!=t.1).map (fun c => subtract c.2 g.2) := by
      apply List.mem_map.mpr;exact ⟨c,by simp [hc,hw],rfl⟩
    have hp := hs _ hd
    have hdelta := subtract_score c.2 g.2 (values w) l (hlen c hc g hmem)
    dsimp [score,evalDelta] at *
    linarith
theorem combine_iff (xs : List (List (List Delta))) (P : Delta → Prop) :
    (∃b∈combine xs,∀d∈b,P d) ↔ ∀x∈xs,∃b∈x,∀d∈b,P d := by
  induction xs with
  | nil => simp [combine]
  | cons x xs ih =>
    constructor
    · rintro ⟨b,hb,hp⟩
      obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hb
      have hpa : ∀d∈a,P d := by intro d hd;exact hp d (List.mem_append_left z hd)
      have hpz : ∀d∈z,P d := by intro d hd;exact hp d (List.mem_append_right a hd)
      have htail := ih.mp ⟨z,hz,hpz⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact ⟨a,ha,hpa⟩
      · exact htail c hc
    · intro h
      obtain ⟨a,ha,hpa⟩ := h x (by simp)
      have htail : ∀c∈xs,∃b∈c,∀d∈b,P d := by intro c hc;exact h c (by simp [hc])
      obtain ⟨z,hz,hpz⟩ := ih.mpr htail
      refine ⟨a++z,?_,?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨a,ha,?_⟩
        exact List.mem_map.mpr ⟨z,hz,rfl⟩
      · intro d hd
        rcases List.mem_append.mp hd with hd|hd
        · exact hpa d hd
        · exact hpz d hd
theorem table_lengths (p : Pattern) (ms : List Mode) (sub : Bool) :
    ∀t∈tables p ms sub,∀a∈t.2,∀b∈t.2,a.2.length=b.2.length := by
  intro t ht
  obtain ⟨obs,ho,rfl⟩ := List.mem_map.mp ht
  intro a ha b hb
  obtain ⟨sa,hsa,rfl⟩ := List.mem_map.mp ha
  obtain ⟨sb,hsb,rfl⟩ := List.mem_map.mp hb
  simp [coefficients]
theorem full_iff_systems (p : Pattern) (ms : List Mode) (sub : Bool) (w : Weights) (l : ℝ) :
    FullSelection p ms sub w l ↔ SystemHolds (systems (tables p ms sub)) w l := by
  rw [full_iff]
  simp only [SystemHolds,systems,combine_iff]
  constructor
  · intro h x hx
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
    exact (separation_iff_input t w l (table_lengths p ms sub t ht)).mp (h t ht)
  · intro h t ht
    exact (separation_iff_input t w l (table_lengths p ms sub t ht)).mpr (h _ (List.mem_map.mpr ⟨t,ht,rfl⟩))
end InteractionTypology
