import PhonologicalOpacity.Attenuation.Productive.Baseline.ProductiveFamily
namespace ProductiveGua
open Retained
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def active (u : Input) (k q : Nat) : Bool :=
 let r := Retained.read u u.origin k q
 r.context && r.defined && !r.good

def familyMarkedWeights (k : Nat) : Nat := if k==4 then 2 else 4

def markedWith (u : Input) (W : Nat → Nat) (s : List String) : Nat × Nat :=
  ((positions u).map fun q =>
    ([4,5,6,7].map fun k =>
      let r := Retained.read u s k q
      let a := active u k q
      let p := r.defined && !r.good
      (if p && a then W k else 0, if p && !a && r.context then W k else 0)).foldl
       (fun acc v => (acc.1+v.1,acc.2+v.2)) (0,0)).foldl
       (fun acc v => (acc.1+v.1,acc.2+v.2)) (0,0)

theorem markedWith_family (u : Input) (s : List String) :
    markedWith u familyMarkedWeights s = marked u s := rfl

def oldContribution (u : Input) (W : Nat → Nat) (s : List String) (q k : Nat) : Nat :=
 let r := Retained.read u s k q
 if (r.defined && !r.good) && active u k q then W k else 0

def oldAt (u : Input) (W : Nat → Nat) (s : List String) (q : Nat) : Nat :=
 ([4,5,6,7].map fun k => oldContribution u W s q k).sum

def localAt (u : Input) (W : Nat → Nat) (q : Nat) (x : String) : Nat :=
 (if ((ft x).nuclear && !((ft x).atr == some true)) && active u 4 q then W 4 else 0)+
 (if (ft x).nuclear && active u 6 q then W 6 else 0)+
 (if (ft x).present && active u 7 q then W 7 else 0)

theorem localAt_le_oldAt (u : Input) (W : Nat → Nat) (s : List String) (q : Nat) :
    localAt u W q s[q]! ≤ oldAt u W s q := by
  simp only [localAt,oldAt,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    oldContribution,Retained.read,Bool.true_and,Bool.not_not]
  norm_num at *
  omega

theorem marked_old_sum (u : Input) (W : Nat → Nat) (s : List String) :
    (markedWith u W s).1 = ((positions u).map (oldAt u W s)).sum := by
  unfold oldAt
  simp [markedWith,fold_pairs,oldContribution,active,List.map_map,Function.comp_def,Nat.add_assoc]

def localPrefix (u : Input) (W : Nat → Nat) (pre : List String) : Nat :=
 ((positions u).map fun q => if q<pre.length then localAt u W q pre[q]! else 0).sum

theorem localPrefix_le_marked (u : Input) (W : Nat → Nat) (pre suffix : List String) :
    localPrefix u W pre ≤ (markedWith u W (pre++suffix)).1 := by
  rw [marked_old_sum]
  unfold localPrefix
  apply List.sum_le_sum
  intro q hq
  by_cases h : q<pre.length
  · simp only [if_pos h]
    have he : (pre++suffix)[q]! = pre[q]! := by
      rw [List.getElem!_eq_getElem?_getD,List.getElem!_eq_getElem?_getD,List.getElem?_append_left h]
    rw [← he]
    exact localAt_le_oldAt u W (pre++suffix) q
  · simp [h]

def prunablePlus (u : Input) (g0 g1 : Int) (pre : List String) : Bool :=
 let f := faithSum u 0 pre
 let m := localPrefix u familyMarkedWeights pre
 decide (g0 < (f.1+m : Int) ∧ 2*g0+g1 ≤ 2*(f.2+m : Int))

theorem prunablePlus_sound {u : Input} {g0 g1 : Int} {pre suffix : List String}
    (h : prunablePlus u g0 g1 pre=true) (l : ℝ) (h0 : 0≤l) (h1 : l<1/2) :
    (g0:ℝ)+g1*l < score u l (pre++suffix) := by
  have h : g0 < ((faithSum u 0 pre).1 : Int)+localPrefix u familyMarkedWeights pre ∧
      2*g0+g1 ≤ 2*((faithSum u 0 pre).2+localPrefix u familyMarkedWeights pre : Int) := by
    simpa [prunablePlus] using h
  have ha : (0:ℝ)<(faithSum u 0 pre).1+localPrefix u familyMarkedWeights pre-g0 := by
    have : (0:Int)<(faithSum u 0 pre).1+localPrefix u familyMarkedWeights pre-g0 := by omega
    exact_mod_cast this
  have hb : (0:ℝ)≤2*((faithSum u 0 pre).2+localPrefix u familyMarkedWeights pre)-2*g0-g1 := by
    have : (0:Int)≤2*((faithSum u 0 pre).2+localPrefix u familyMarkedWeights pre)-2*g0-g1 := by omega
    exact_mod_cast this
  have hm : (localPrefix u familyMarkedWeights pre : ℝ)≤(marked u (pre++suffix)).1 := by
    have hh := localPrefix_le_marked u familyMarkedWeights pre suffix
    rw [markedWith_family] at hh
    exact_mod_cast hh
  have ht : 0<1-2*l := by linarith
  have hA := mul_pos ha ht
  have hB := mul_nonneg hb h0
  have hF0 := mul_nonneg (le_of_lt ht) (Nat.cast_nonneg (faithSum u pre.length suffix).1 : (0:ℝ)≤_)
  have hF1 := mul_nonneg h0 (Nat.cast_nonneg (faithSum u pre.length suffix).2 : (0:ℝ)≤_)
  have hM1 := mul_nonneg h0 (Nat.cast_nonneg (marked u (pre++suffix)).2 : (0:ℝ)≤_)
  dsimp [score]
  rw [faithSum_append]
  simp only [Nat.zero_add,Nat.cast_add]
  nlinarith
end ProductiveGua
