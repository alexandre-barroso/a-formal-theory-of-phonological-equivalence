import PhonologicalOpacity.Gua.Reader

namespace ProductiveSubjectGua
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def faith (u : Input) (q : Nat) (x : String) : Nat × Nat :=
  let f := ft x
  let r := ft u.origin[q]!
  let mx := if f.present then 0 else 1
  let atrn := if f.nuclear && r.nuclear && f.atr != r.atr then 1 else 0
  let qu := if f.present && f.quality.isSome && r.quality.isSome && f.quality != r.quality then 1 else 0
  let nu := if f.present && f.nuclear != r.nuclear then 1 else 0
  let initial := r.nuclear && (q == 0 || word u (q-1) != word u q)
  let ini := if initial && f.present && f.quality.isSome &&
    !(f.quality == r.quality && (!f.nuclear || f.atr == r.atr)) then 1 else 0
  (3*mx+atrn+qu+2*nu+4*ini, mx+atrn+nu+4*ini)

def faithSum (u : Input) : Nat → List String → Nat × Nat
  | _, [] => (0,0)
  | q, x::xs => let f := faith u q x; let r := faithSum u (q+1) xs; (f.1+r.1,f.2+r.2)

theorem faithSum_append (u : Input) (a b : List String) (q : Nat) :
    faithSum u q (a++b) =
    ((faithSum u q a).1+(faithSum u (q+a.length) b).1,
     (faithSum u q a).2+(faithSum u (q+a.length) b).2) := by
  induction a generalizing q with
  | nil => simp [faithSum]
  | cons x xs ih =>
    simp [faithSum, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def marked (u : Input) (s : List String) : Nat × Nat :=
  ((positions u).map fun q =>
    ([4,5,6,7].map fun k =>
      let r := read u s k q
      let r0 := read u u.origin k q
      let a := r0.context && r0.defined && !r0.good &&
        (if k == 5 then nextLive u s q == nextLive u u.origin q else true)
      let p := (if k == 5 then (nextLive u s q).any (fun j => word u j == word u q + 1 && samePhrase u q j) else r.defined) && !r.good
      let w := if k == 4 then 2 else 4
      (if p && a then w else 0, if p && !a && r.context then w else 0)).foldl
       (fun acc v => (acc.1+v.1,acc.2+v.2)) (0,0)).foldl
       (fun acc v => (acc.1+v.1,acc.2+v.2)) (0,0)

noncomputable def score (u : Input) (l : ℝ) (s : List String) : ℝ :=
  let f := faithSum u 0 s
  let m := marked u s
  (1-2*l)*f.1+2*l*f.2+m.1+l*m.2

def margin (u : Input) (g0 g1 : Int) (s : List String) : Bool :=
  let f := faithSum u 0 s
  let m := marked u s
  let a : Int := f.1+m.1-g0
  let b : Int := 2*(f.2 : Int)-2*(f.1 : Int)+m.2-g1
  decide (0<a ∧ 0≤2*a+b)

def prunable (u : Input) (g0 g1 : Int) (pre : List String) : Bool :=
  let f := faithSum u 0 pre
  decide (g0 < (f.1 : Int) ∧ 2*g0+g1 ≤ 2*(f.2 : Int))

def observe (s : List String) : String := String.join (s.filter (fun x => x != "∅"))

def check (u : Input) (g0 g1 : Int) (out : String) (pre : List String) : List (List String) → Bool
  | [] => if observe pre == out then true else margin u g0 g1 pre
  | opts::rest => if prunable u g0 g1 pre then true else
      opts.all (fun x => check u g0 g1 out (pre++[x]) rest)

def Generated : List (List String) → List String → Prop
  | [], s => s=[]
  | opts::rest, [] => False
  | opts::rest, x::xs => x ∈ opts ∧ Generated rest xs

theorem margin_sound {u : Input} {g0 g1 : Int} {s : List String}
    (h : margin u g0 g1 s = true) (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    (g0 : ℝ)+g1*l < score u l s := by
  have h : 0 < ((faithSum u 0 s).1 : Int)+(marked u s).1-g0 ∧
      0 ≤ 2*(((faithSum u 0 s).1 : Int)+(marked u s).1-g0)+
       (2*((faithSum u 0 s).2 : Int)-2*((faithSum u 0 s).1 : Int)+(marked u s).2-g1) := by
    simpa [margin] using h
  have ha : (0:ℝ) < (faithSum u 0 s).1+(marked u s).1-g0 := by exact_mod_cast h.1
  have hb : (0:ℝ) ≤ 2*((faithSum u 0 s).1+(marked u s).1-g0)+
      (2*(faithSum u 0 s).2-2*(faithSum u 0 s).1+(marked u s).2-g1) := by exact_mod_cast h.2
  have ht : 0 < 1-2*l := by linarith
  have hA := mul_pos ha ht
  have hB := mul_nonneg hb h0
  dsimp [score]
  nlinarith

theorem prunable_sound {u : Input} {g0 g1 : Int} {pre suffix : List String}
    (h : prunable u g0 g1 pre = true) (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    (g0 : ℝ)+g1*l < score u l (pre++suffix) := by
  have h : g0 < ((faithSum u 0 pre).1 : Int) ∧
      2*g0+g1 ≤ 2*((faithSum u 0 pre).2 : Int) := by simpa [prunable] using h
  have ha : (0:ℝ) < (faithSum u 0 pre).1-g0 := by exact_mod_cast (sub_pos.mpr h.1)
  have hb : (0:ℝ) ≤ 2*(faithSum u 0 pre).2-2*g0-g1 := by
    have hh : (0:Int) ≤ 2*((faithSum u 0 pre).2 : Int)-2*g0-g1 := by omega
    exact_mod_cast hh
  have ht : 0 < 1-2*l := by linarith
  have hA := mul_pos ha ht
  have hB := mul_nonneg hb h0
  have hf0 : (0:ℝ) ≤ (faithSum u pre.length suffix).1 := Nat.cast_nonneg _
  have hf1 : (0:ℝ) ≤ (faithSum u pre.length suffix).2 := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ (marked u (pre++suffix)).1 := Nat.cast_nonneg _
  have hm1 : (0:ℝ) ≤ (marked u (pre++suffix)).2 := Nat.cast_nonneg _
  have hF0 := mul_nonneg (le_of_lt ht) hf0
  have hF1 := mul_nonneg h0 hf1
  have hM1 := mul_nonneg h0 hm1
  dsimp [score]
  rw [faithSum_append]
  simp only [Nat.zero_add, Nat.cast_add]
  nlinarith

theorem check_sound {u : Input} {g0 g1 : Int} {out : String} {pre suffix : List String}
    {rows : List (List String)} (h : check u g0 g1 out pre rows = true)
    (hs : Generated rows suffix) (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    observe (pre++suffix)=out ∨ (g0:ℝ)+g1*l < score u l (pre++suffix) := by
  induction rows generalizing pre suffix with
  | nil =>
    have he : suffix=[] := hs
    subst suffix
    simp only [List.append_nil]
    by_cases ho : observe pre=out
    · exact Or.inl ho
    · right
      have hm : margin u g0 g1 pre = true := by simpa [check,ho] using h
      exact margin_sound hm l h0 h1
  | cons opts rest ih =>
    by_cases hp : prunable u g0 g1 pre = true
    · exact Or.inr (prunable_sound hp l h0 h1)
    · have hh : opts.all (fun x => check u g0 g1 out (pre++[x]) rest) = true := by
        simpa [check,hp] using h
      cases suffix with
      | nil => exact False.elim hs
      | cons x xs =>
        have hx : x ∈ opts ∧ Generated rest xs := hs
        have hc := List.all_eq_true.mp hh x hx.1
        simpa only [List.append_assoc,List.singleton_append] using ih hc hx.2

end ProductiveSubjectGua
