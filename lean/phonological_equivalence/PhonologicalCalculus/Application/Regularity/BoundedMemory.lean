                     
                   
import Mathlib.Tactic
import Mathlib.Computability.MyhillNerode

namespace BoundedMemory

structure Machine (Q A I : Type) where
  start : Q
  step : Q → A → Q
  weight : Q → A → ℕ
  final : Q → ℕ
  input : A → I
  allowed : A → Prop

namespace Machine
variable {Q A I : Type} (M : Machine Q A I)

def state (q : Q) (xs : List A) : Q := xs.foldl M.step q

def cost : Q → List A → ℕ
  | _, [] => 0
  | q, a :: xs => M.weight q a + cost (M.step q a) xs

def total (q : Q) (xs : List A) : ℕ := M.cost q xs + M.final (M.state q xs)
def valid (xs : List A) : Prop := ∀ a ∈ xs, M.allowed a
def same (xs ys : List A) : Prop := xs.map M.input = ys.map M.input
def winner (xs : List A) : Prop := M.valid xs ∧
  ∀ ys, M.valid ys → M.same ys xs → M.total M.start xs ≤ M.total M.start ys

@[simp] theorem state_append (q : Q) (xs ys : List A) :
    M.state q (xs ++ ys) = M.state (M.state q xs) ys := by
  simp [state,List.foldl_append]

theorem cost_append (q : Q) (xs ys : List A) :
    M.cost q (xs ++ ys) = M.cost q xs + M.cost (M.state q xs) ys := by
  induction xs generalizing q with
  | nil => simp [cost,state]
  | cons a xs ih => simpa [cost,state,List.foldl_cons,Nat.add_assoc] using congrArg (M.weight q a + ·) (ih (M.step q a))

theorem total_append (q : Q) (xs ys : List A) :
    M.total q (xs ++ ys) = M.cost q xs + M.total (M.state q xs) ys := by
  simp [total,cost_append,Nat.add_assoc]

@[simp] theorem valid_append (xs ys : List A) :
    M.valid (xs ++ ys) ↔ M.valid xs ∧ M.valid ys := by simp only [valid,List.mem_append]; aesop

theorem same_append {x y z v : List A} (h : M.same x y) (k : M.same z v) :
    M.same (x ++ z) (y ++ v) := by simp_all [same]

noncomputable def base (xs : List A) : ℕ :=
  sInf {n | ∃ ys, M.valid ys ∧ M.same ys xs ∧ M.cost M.start ys = n}

theorem base_le {xs ys : List A} (hy : M.valid ys) (hs : M.same ys xs) :
    M.base xs ≤ M.cost M.start ys := by
  exact Nat.sInf_le ⟨ys,hy,hs,rfl⟩

theorem base_attained {xs : List A} (hx : M.valid xs) :
    ∃ ys, M.valid ys ∧ M.same ys xs ∧ M.cost M.start ys = M.base xs := by
  exact Nat.sInf_mem (s := {n | ∃ ys, M.valid ys ∧ M.same ys xs ∧ M.cost M.start ys = n}) ⟨M.cost M.start xs,xs,hx,rfl,rfl⟩

def bounded (K : ℕ) : Prop := ∀ (q r : Q) (xs : List A), M.total q xs ≤ M.total r xs + K

theorem optimal_prefix_bound (K : ℕ) (hb : M.bounded K) {xs zs : List A}
    (h : M.winner (xs ++ zs)) : M.cost M.start xs ≤ M.base xs + K := by
  have hv := (M.valid_append xs zs).mp h.1
  obtain ⟨ys,hy,hs,hcost⟩ := M.base_attained hv.1
  have ho := h.2 (ys ++ zs) ((M.valid_append _ _).mpr ⟨hy,hv.2⟩) (M.same_append hs rfl)
  rw [M.total_append,M.total_append,hcost] at ho
  have ht := hb (M.state M.start ys) (M.state M.start xs) zs
  omega

abbrev Signature (Q : Type) (K : ℕ) := Option (Q × Fin (K+1) × Set (Q × Fin (K+1)))

noncomputable def signature (K : ℕ) (xs : List A) : Signature Q K := by
  classical
  exact if h : M.valid xs ∧ M.cost M.start xs ≤ M.base xs + K then
    some (M.state M.start xs,⟨M.cost M.start xs - M.base xs,by omega⟩,
      {p | ∃ ys, M.valid ys ∧ M.same ys xs ∧ M.state M.start ys = p.1 ∧ M.cost M.start ys = M.base xs + p.2.val})
    else none

def continuation (K : ℕ) (s : Signature Q K) (zs : List A) : Prop :=
  match s with
  | none => False
  | some (q,r,S) => M.valid zs ∧ ∀ p ∈ S, ∀ vs, M.valid vs → M.same vs zs →
      r.val + M.total q zs ≤ p.2.val + M.total p.1 vs

theorem split_competitor {xs zs ys : List A} (h : M.same ys (xs ++ zs)) :
    ∃ ps vs, ys = ps ++ vs ∧ M.same ps xs ∧ M.same vs zs := by
  refine ⟨ys.take xs.length,ys.drop xs.length,(List.take_append_drop _ _).symm,?_,?_⟩
  · have := congrArg (List.take xs.length) h
    simpa [same,List.map_take] using this
  · have := congrArg (List.drop xs.length) h
    simpa [same,List.map_drop] using this

theorem winner_iff_continuation (K : ℕ) (hb : M.bounded K) (xs zs : List A) :
    M.winner (xs ++ zs) ↔ M.continuation K (M.signature K xs) zs := by
  classical
  unfold signature
  split_ifs with hx
  · rcases hx with ⟨hx,hbound⟩
    have hbase := M.base_le hx (show M.same xs xs from rfl)
    simp only [continuation]
    constructor
    · intro hw
      refine ⟨((M.valid_append _ _).mp hw.1).2,?_⟩
      rintro ⟨q,r⟩ ⟨ys,hy,hs,hq,hc⟩ vs hv hvs
      have ho := hw.2 (ys ++ vs) ((M.valid_append _ _).mpr ⟨hy,hv⟩) (M.same_append hs hvs)
      rw [M.total_append,M.total_append,hq,hc] at ho
      dsimp at ho ⊢
      omega
    · rintro ⟨hz,htest⟩
      refine ⟨(M.valid_append _ _).mpr ⟨hx,hz⟩,?_⟩
      intro ys hy hs
      obtain ⟨ps,vs,rfl,hps,hvs⟩ := M.split_competitor hs
      rcases (M.valid_append _ _).mp hy with ⟨hp,hv⟩
      rw [M.total_append,M.total_append]
      by_cases hpbound : M.cost M.start ps ≤ M.base xs + K
      · have hpbase := M.base_le hp hps
        let r : Fin (K+1) := ⟨M.cost M.start ps - M.base xs,by omega⟩
        have member : (M.state M.start ps,r) ∈
            {p | ∃ ys, M.valid ys ∧ M.same ys xs ∧ M.state M.start ys = p.1 ∧ M.cost M.start ys = M.base xs + p.2.val} :=
          ⟨ps,hp,hps,rfl,by dsimp [r]; omega⟩
        have h := htest _ member vs hv hvs
        dsimp [r] at h
        omega
      · obtain ⟨bs,hbs,hsbs,hcb⟩ := M.base_attained hx
        have member : (M.state M.start bs,(0 : Fin (K+1))) ∈
            {p | ∃ ys, M.valid ys ∧ M.same ys xs ∧ M.state M.start ys = p.1 ∧ M.cost M.start ys = M.base xs + p.2.val} :=
          ⟨bs,hbs,hsbs,rfl,by simpa using hcb⟩
        have h := htest _ member vs hv hvs
        have b := hb (M.state M.start bs) (M.state M.start ps) vs
        dsimp at h
        omega
  · simp only [continuation,iff_false]
    intro h
    exact hx ⟨((M.valid_append _ _).mp h.1).1,M.optimal_prefix_bound K hb h⟩

theorem regular_winners [Finite Q] (K : ℕ) (hb : M.bounded K) :
    Language.IsRegular {xs | M.winner xs} := by
  classical
  apply Language.IsRegular.of_finite_range_leftQuotient
  have hs : Set.Finite (Set.range (fun s : Signature Q K => (M.continuation K s : Language A))) := Set.finite_range _
  apply hs.subset
  rintro l ⟨xs,rfl⟩
  refine ⟨M.signature K xs,?_⟩
  ext zs
  exact (M.winner_iff_continuation K hb xs zs).symm

end Machine
end BoundedMemory
