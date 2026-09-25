                  
import PhonologicalOpacity.Attenuation.Productive.Subject.ProductiveFamily
namespace ProductiveSubjectGua
open Retained
set_option maxHeartbeats 0
noncomputable def readerFaithAt (u : Input) (w : Fin 9 → ℝ) (s : List String) (q : Nat) : ℝ :=
  ([0,1,2,3,8].map fun k : Fin 9 =>
    let r := read u s k q
    w k * (if r.context && r.defined && !r.good then 1 else 0)).sum

theorem faithAt_reader (u : Input) (w : Fin 9 → ℝ) (s : List String) (q : Nat) :
    faithAt u w q s[q]! = readerFaithAt u w s q := by
  simp [readerFaithAt, Retained.read, faithAt, Fin.val_ofNat]
  split_ifs <;> simp_all <;> ring

theorem fullFaith_append (u : Input) (w : Fin 9 → ℝ) (q : Nat) (s t : List String) :
    fullFaith u w q (s++t)=fullFaith u w q s+fullFaith u w (q+s.length) t := by
  induction s generalizing q with
  | nil => simp [fullFaith]
  | cons x xs ih => simp [fullFaith,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,add_assoc]

theorem fullFaith_positions (u : Input) (w : Fin 9 → ℝ) (s : List String) :
    fullFaith u w 0 s = ((List.range s.length).map (fun q => faithAt u w q s[q]!)).sum := by
  induction s using List.reverseRecOn with
  | nil => simp [fullFaith]
  | append_singleton s x ih =>
    rw [fullFaith_append,ih]
    simp only [List.length_append,List.length_singleton,List.range_succ,List.map_append,
      List.map_singleton,List.sum_append,List.sum_singleton,fullFaith,Nat.zero_add,add_zero]
    congr 1
    · apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      have hq : q<s.length := List.mem_range.mp hq
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hq]
    · simp

noncomputable def readerScore (u : Input) (w : Fin 9 → ℝ) (l : ℝ) (s : List String) : ℝ :=
  ((positions u).map (readerFaithAt u w s)).sum+fullMarked u w l s

theorem fullScore_reader (u : Input) (w : Fin 9 → ℝ) (l : ℝ) (s : List String)
    (h : s.length=u.origin.length) : fullScore u w l s=readerScore u w l s := by
  rw [fullScore,fullFaith_positions]
  simp only [readerScore,positions,← h,faithAt_reader]

#print axioms fullScore_reader
end ProductiveSubjectGua
