                  
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

namespace GappedScope

noncomputable section

def siteCost (i v l : ℝ) (old current : Bool) : ℝ :=
  (if old = current then 0 else i) +
  (if current then if old then v else l * v else 0)

def segmentCost (i v l : ℝ) : List Bool → List Bool → ℝ
  | a :: as, b :: bs => siteCost i v l a b + segmentCost i v l as bs
  | _, _ => 0

def agreementCost (a l : ℝ) : List Bool → List Bool → ℝ
  | u :: un :: us, y :: yn :: ys =>
      (if y = yn then 0 else if u = un then l * a else a) +
        agreementCost a l (un :: us) (yn :: ys)
  | _, _ => 0

def input (n : ℕ) : List Bool := List.replicate n false ++ [true]
def voiced (n : ℕ) : List Bool := List.replicate n true ++ [true]
def voiceless (n : ℕ) : List Bool := List.replicate n false ++ [false]

def clusterCost (i p v a l : ℝ) (u y : List Bool) : ℝ :=
  segmentCost i v l u y + agreementCost a l u y +
    (if u.getLast? = y.getLast? then 0 else p)

theorem candidates_length (n : ℕ) :
    (input n).length = n + 1 ∧ (voiced n).length = n + 1 ∧
      (voiceless n).length = n + 1 := by
  simp [input, voiced, voiceless]

theorem segment_voiced (i v l : ℝ) (n : ℕ) :
    segmentCost i v l (input n) (voiced n) = n * (i + l * v) + v := by
  induction n with
  | zero => simp [input, voiced, segmentCost, siteCost]
  | succ n ih =>
    simpa [input, voiced, List.replicate_succ, segmentCost, siteCost,
      Nat.cast_add, Nat.cast_one, add_mul, add_assoc, add_comm, add_left_comm] using
      congrArg (fun x : ℝ => i + l * v + x) ih

theorem segment_voiceless (i v l : ℝ) (n : ℕ) :
    segmentCost i v l (input n) (voiceless n) = i := by
  induction n with
  | zero => simp [input, voiceless, segmentCost, siteCost]
  | succ n ih => simpa [input, voiceless, List.replicate_succ, segmentCost, siteCost] using ih

theorem agreement_uniform (a l : ℝ) (u : List Bool) (b : Bool) (n : ℕ) :
    agreementCost a l u (List.replicate n b) = 0 := by
  induction n generalizing u with
  | zero => cases u with
    | nil => rfl
    | cons x xs => cases xs <;> rfl
  | succ n ih =>
    cases n with
    | zero => cases u with
      | nil => rfl
      | cons x xs => cases xs <;> rfl
    | succ n =>
      cases u with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons x' xs =>
          simpa [List.replicate_succ, agreementCost] using ih (x' :: xs)

theorem voiced_score (i p v a l : ℝ) (n : ℕ) :
    clusterCost i p v a l (input n) (voiced n) = n * (i + l * v) + v := by
  have h : voiced n = List.replicate (n + 1) true := by simp [voiced, List.replicate_add]
  unfold clusterCost
  rw [segment_voiced]
  have ha : agreementCost a l (input n) (voiced n) = 0 := by
    rw [h]
    exact agreement_uniform a l (input n) true (n + 1)
  rw [ha]
  simp [input, voiced, List.getLast?_append]

theorem voiceless_score (i p v a l : ℝ) (n : ℕ) :
    clusterCost i p v a l (input n) (voiceless n) = i + p := by
  have h : voiceless n = List.replicate (n + 1) false := by simp [voiceless, List.replicate_add]
  unfold clusterCost
  rw [segment_voiceless]
  have ha : agreementCost a l (input n) (voiceless n) = 0 := by
    rw [h]
    exact agreement_uniform a l (input n) false (n + 1)
  rw [ha]
  simp [input, voiceless, List.getLast?_append]

theorem unbounded_competitor (i p v a l : ℝ) (hk : 0 < i + l * v) :
    ∃ n : ℕ, clusterCost i p v a l (input n) (voiceless n) <
      clusterCost i p v a l (input n) (voiced n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((i + p - v) / (i + l * v))
  refine ⟨n, ?_⟩
  rw [voiceless_score, voiced_score]
  have := (div_lt_iff₀ hk).1 hn
  linarith

theorem final_stop_scores (i v l : ℝ) :
    segmentCost i v l [false] [false] = 0 ∧
      segmentCost i v l [false] [true] = i + l * v := by
  simp [segmentCost, siteCost]

theorem no_fixed_uniform_grammar (i p v a l : ℝ) :
    ¬ (segmentCost i v l [false] [false] < segmentCost i v l [false] [true] ∧
      ∀ n, clusterCost i p v a l (input n) (voiced n) ≤
        clusterCost i p v a l (input n) (voiceless n)) := by
  intro h
  have hk : 0 < i + l * v := by simpa [segmentCost, siteCost] using h.1
  obtain ⟨n, hn⟩ := unbounded_competitor i p v a l hk
  exact (not_lt_of_ge (h.2 n)) hn

theorem russian_retained_witness :
    clusterCost 1 80 4 80 (1/8) (input 52) (voiceless 52) = 81 ∧
    clusterCost 1 80 4 80 (1/8) (input 52) (voiced 52) = 82 := by
  rw [voiceless_score, voiced_score]
  norm_num

end
end GappedScope
