import PhonologicalOpacity.Attenuation.Productive.Baseline.ProductiveTheory
namespace ProductiveGua
open Retained
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def weightFamily (l : ℝ) : Fin 9 → ℝ := ![3-4*l,1,1-2*l,2-2*l,2,4,4,4,4]
noncomputable def faithAt (u : Input) (w : Fin 9 → ℝ) (q : Nat) (x : String) : ℝ :=
  let f := ft x
  let r := ft u.origin[q]!
  let mx : Nat := if f.present then 0 else 1
  let atrn : Nat := if f.nuclear && r.nuclear && f.atr != r.atr then 1 else 0
  let qu : Nat := if f.present && f.quality.isSome && r.quality.isSome && f.quality != r.quality then 1 else 0
  let nu : Nat := if f.present && f.nuclear != r.nuclear then 1 else 0
  let initial := r.nuclear && (q == 0 || word u (q-1) != word u q)
  let ini : Nat := if initial && f.present && f.quality.isSome &&
    !(f.quality == r.quality && (!f.nuclear || f.atr == r.atr)) then 1 else 0
  w 0*mx+w 1*atrn+w 2*qu+w 3*nu+w 8*ini

noncomputable def fullFaith (u : Input) (w : Fin 9 → ℝ) : Nat → List String → ℝ
 | _,[] => 0
 | q,x::xs => faithAt u w q x + fullFaith u w (q+1) xs

noncomputable def fullMarked (u : Input) (w : Fin 9 → ℝ) (l : ℝ) (s : List String) : ℝ :=
 ((positions u).map fun q =>
   ([4,5,6,7].map fun k : Fin 9 =>
     let r := read u s k q
     let r0 := read u u.origin k q
     let a := r0.context && r0.defined && !r0.good
     let p := r.defined && !r.good
     w k*((if p && a then 1 else 0) + l*(if p && !a && r.context then 1 else 0))).sum).sum

noncomputable def fullScore (u : Input) (w : Fin 9 → ℝ) (l : ℝ) (s : List String) : ℝ :=
 fullFaith u w 0 s + fullMarked u w l s

theorem faithAt_family (u : Input) (q : Nat) (x : String) (l : ℝ) :
    faithAt u (weightFamily l) q x = (1-2*l)*(faith u q x).1+2*l*(faith u q x).2 := by
  simp only [faithAt,faith,weightFamily,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
  push_cast
  ring

theorem fullFaith_family (u : Input) (q : Nat) (s : List String) (l : ℝ) :
    fullFaith u (weightFamily l) q s = (1-2*l)*(faithSum u q s).1+2*l*(faithSum u q s).2 := by
  induction s generalizing q with
  | nil => simp [fullFaith,faithSum]
  | cons x xs ih =>
    simp only [fullFaith,faithSum,faithAt_family,ih,Nat.cast_add]
    ring

theorem fold_pairs (xs : List (Nat × Nat)) (acc : Nat × Nat) :
    xs.foldl (fun a v => (a.1+v.1,a.2+v.2)) acc =
      (acc.1+(xs.map Prod.fst).sum,acc.2+(xs.map Prod.snd).sum) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

theorem eval_pair_fold (xs : List (Nat × Nat)) (l : ℝ) :
    ((xs.foldl (fun (a v : Nat × Nat) => (a.1+v.1,a.2+v.2)) (0,0)).1 : ℝ) +
      l*((xs.foldl (fun (a v : Nat × Nat) => (a.1+v.1,a.2+v.2)) (0,0)).2 : ℝ) =
    (xs.map (fun p => (p.1 : ℝ)+l*p.2)).sum := by
  rw [fold_pairs]
  simp only [Nat.zero_add]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    rw [← ih]
    ring

theorem term_weight (w : Nat) (p a c : Bool) (l : ℝ) :
    ((if p && a then w else 0 : Nat) : ℝ)+l*((if p && !a && c then w else 0 : Nat) : ℝ) =
    (w:ℝ)*((if p && a then 1 else 0)+l*(if p && !a && c then 1 else 0)) := by
  split_ifs <;> simp <;> ring

theorem fullMarked_family (u : Input) (s : List String) (l : ℝ) :
    fullMarked u (weightFamily l) l s = (marked u s).1 + l*(marked u s).2 := by
  have h4 : weightFamily l 4 = 2 := rfl
  have h5 : weightFamily l 5 = 4 := rfl
  have h6 : weightFamily l 6 = 4 := rfl
  have h7 : weightFamily l 7 = 4 := rfl
  unfold marked
  rw [eval_pair_fold]
  simp only [List.map_map]
  unfold fullMarked
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  simp only [Function.comp_apply]
  rw [eval_pair_fold]
  simp only [List.map_map,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [term_weight,h4,h5,h6,h7]
  norm_num

theorem fullScore_family (u : Input) (s : List String) (l : ℝ) :
    fullScore u (weightFamily l) l s = score u l s := by
  rw [fullScore,fullFaith_family,fullMarked_family]
  simp only [score]
  ring

theorem weightFamily_nonnegative (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    ∀ k, 0 ≤ weightFamily l k := by
  intro k
  fin_cases k <;> simp [weightFamily] <;> linarith

end ProductiveGua
