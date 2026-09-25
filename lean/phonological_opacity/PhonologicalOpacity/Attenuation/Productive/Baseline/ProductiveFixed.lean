import PhonologicalOpacity.Attenuation.Productive.Baseline.ProductiveLowerBound
import PhonologicalOpacity.Attenuation.Productive.Baseline.ProductiveSelection
namespace ProductiveGua
open Retained
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def oldNatural (k : Nat) : Nat := [20,1,1,2,4,8,8,24,1][k]!
noncomputable def oldWeights (k : Fin 9) : ℝ := oldNatural k

theorem fullMarked_natural (u : Input) (W : Nat → Nat) (l : ℝ) (s : List String) :
    fullMarked u (fun k => (W k : ℝ)) l s =
      (markedWith u W s).1+l*(markedWith u W s).2 := by
  unfold markedWith
  rw [eval_pair_fold]
  simp only [List.map_map]
  unfold fullMarked
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  simp only [Function.comp_apply]
  rw [eval_pair_fold]
  simp only [List.map_map,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Function.comp_apply,term_weight]
  rfl

def fixedFaith (u : Input) (q : Nat) (x : String) : Nat :=
 let f := ft x
 let r := ft u.origin[q]!
 let mx := if f.present then 0 else 1
 let atrn := if f.nuclear && r.nuclear && f.atr != r.atr then 1 else 0
 let qu := if f.present && f.quality.isSome && r.quality.isSome && f.quality != r.quality then 1 else 0
 let nu := if f.present && f.nuclear != r.nuclear then 1 else 0
 let initial := r.nuclear && (q==0 || word u (q-1)!=word u q)
 let ini := if initial && f.present && f.quality.isSome &&
   !(f.quality==r.quality && (!f.nuclear || f.atr==r.atr)) then 1 else 0
 20*mx+atrn+qu+2*nu+ini

def fixedFaithSum (u : Input) : Nat → List String → Nat
 | _,[] => 0
 | q,x::xs => fixedFaith u q x+fixedFaithSum u (q+1) xs

theorem fixedFaith_bridge (u : Input) (q : Nat) (x : String) :
    fullFaith u oldWeights q [x] = (fixedFaith u q x : ℝ) := by
  simp only [fullFaith,faithAt,oldWeights,oldNatural,fixedFaith]
  norm_num <;> push_cast <;> ring

theorem fixedFaithSum_bridge (u : Input) (q : Nat) (s : List String) :
    fullFaith u oldWeights q s = (fixedFaithSum u q s : ℝ) := by
  induction s generalizing q with
  | nil => simp [fullFaith,fixedFaithSum]
  | cons x xs ih =>
    have h := fixedFaith_bridge u q x
    simp only [fullFaith,add_zero] at h
    simp only [fullFaith,fixedFaithSum,h,ih,Nat.cast_add]

def fixedScore8 (u : Input) (s : List String) : Nat :=
 8*fixedFaithSum u 0 s+8*(markedWith u oldNatural s).1+(markedWith u oldNatural s).2

theorem fixedScore_bridge (u : Input) (s : List String) :
    8*fullScore u oldWeights (1/8) s = (fixedScore8 u s : ℝ) := by
  rw [fullScore,fixedFaithSum_bridge]
  unfold oldWeights
  rw [fullMarked_natural]
  simp only [fixedScore8,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem fixedFaithSum_append (u : Input) (a b : List String) (q : Nat) :
    fixedFaithSum u q (a++b)=fixedFaithSum u q a+fixedFaithSum u (q+a.length) b := by
  induction a generalizing q with
  | nil => simp [fixedFaithSum]
  | cons x xs ih => simp [fixedFaithSum,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def fixedPrunable (u : Input) (g : Nat) (pre : List String) : Bool :=
 decide (g<8*fixedFaithSum u 0 pre+8*localPrefix u oldNatural pre)

theorem fixedPrunable_sound {u : Input} {g : Nat} {pre suffix : List String}
    (h : fixedPrunable u g pre=true) : g<fixedScore8 u (pre++suffix) := by
  have h : g<8*fixedFaithSum u 0 pre+8*localPrefix u oldNatural pre := by
    simpa [fixedPrunable] using h
  have hm := localPrefix_le_marked u oldNatural pre suffix
  unfold fixedScore8
  rw [fixedFaithSum_append]
  omega

def fixedCheck (u : Input) (g : Nat) (goal pre : List String) : List (List String) → Bool
 | [] => if pre==goal then true else decide (g<fixedScore8 u pre)
 | opts::rest => if fixedPrunable u g pre then true else
      opts.all (fun x => fixedCheck u g goal (pre++[x]) rest)

theorem fixedCheck_sound {u : Input} {g : Nat} {goal pre suffix : List String}
    {rows : List (List String)} (h : fixedCheck u g goal pre rows=true)
    (hs : Generated rows suffix) : pre++suffix=goal ∨ g<fixedScore8 u (pre++suffix) := by
  induction rows generalizing pre suffix with
  | nil =>
    have he : suffix=[] := hs
    subst suffix
    simp only [List.append_nil]
    by_cases he : pre=goal
    · exact Or.inl he
    · right
      simpa [fixedCheck,he] using h
  | cons opts rest ih =>
    by_cases hp : fixedPrunable u g pre=true
    · exact Or.inr (fixedPrunable_sound hp)
    · have hh : opts.all (fun x => fixedCheck u g goal (pre++[x]) rest)=true := by
        simpa [fixedCheck,hp] using h
      cases suffix with
      | nil => exact False.elim hs
      | cons x xs =>
        have hx : x∈opts ∧ Generated rest xs := hs
        have hc := List.all_eq_true.mp hh x hx.1
        simpa only [List.append_assoc,List.singleton_append] using ih hc hx.2

theorem fixedCheck_of_children {u : Input} {g : Nat} {goal pre : List String}
    {opts : List String} {rest : List (List String)}
    (h : ∀ x∈opts, fixedCheck u g goal (pre++[x]) rest=true) :
    fixedCheck u g goal pre (opts::rest)=true := by
  simp only [fixedCheck]
  split
  · rfl
  · exact List.all_eq_true.mpr h

theorem fixed_unique_of_check {u : Input} {g : Nat} {goal : List String}
    {rows : List (List String)} (hc : fixedCheck u g goal [] rows=true)
    (hg : Generated rows goal) (hv : fixedScore8 u goal=g) :
    ∀ s, Generated rows s → s≠goal → fullScore u oldWeights (1/8) goal<fullScore u oldWeights (1/8) s := by
  intro s hs hn
  have h := fixedCheck_sound hc hs
  simp only [List.nil_append] at h
  rcases h with he | hlt
  · exact False.elim (hn he)
  · have ht : (g:ℝ)<fixedScore8 u s := by exact_mod_cast hlt
    rw [← hv,← fixedScore_bridge,← fixedScore_bridge] at ht
    linarith
end ProductiveGua
