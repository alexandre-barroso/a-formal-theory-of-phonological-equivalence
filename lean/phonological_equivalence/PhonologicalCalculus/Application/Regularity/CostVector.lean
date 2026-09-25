                   
import PhonologicalCalculus.Application.Regularity.CostApplication

namespace CostVector
open BoundedMemory WeightedCost
variable {Q A I : Type} {K : ℕ}

def Dominates (V W : Control Q K) : Prop :=
  ∀ q r, (q,r) ∈ W → ∃ s, (q,s) ∈ V ∧ s.val ≤ r.val
def Equivalent (V W : Control Q K) : Prop := Dominates V W ∧ Dominates W V

theorem dominates_trans {U V W : Control Q K} (h : Dominates U V) (g : Dominates V W) :
    Dominates U W := by
  intro q r hr
  obtain ⟨s,hs,hsl⟩ := g q r hr
  obtain ⟨t,ht,htl⟩ := h q s hs
  exact ⟨t,ht,htl.trans hsl⟩

theorem equivalent_trans {U V W : Control Q K} (h : Equivalent U V) (g : Equivalent V W) :
    Equivalent U W := ⟨dominates_trans h.1 g.1,dominates_trans g.2 h.2⟩

theorem nonempty_iff {V W : Control Q K} (h : Equivalent V W) : V.Nonempty ↔ W.Nonempty := by
  constructor
  · rintro ⟨⟨q,r⟩,hr⟩; obtain ⟨s,hs,_⟩ := h.2 q r hr; exact ⟨(q,s),hs⟩
  · rintro ⟨⟨q,r⟩,hr⟩; obtain ⟨s,hs,_⟩ := h.1 q r hr; exact ⟨(q,s),hs⟩

variable (M : Machine Q A I)

theorem expanded_dominates {V W : Control Q K} (h : Dominates V W) (i : I)
    {q : Q} {c : ℕ} (hc : (q,c) ∈ expanded M K W i) :
    ∃ d, (q,d) ∈ expanded M K V i ∧ d ≤ c := by
  rcases hc with ⟨p,r,hr,a,ha,hi,he⟩
  obtain ⟨s,hs,hle⟩ := h p r hr
  have hq : q=M.step p a := congrArg Prod.fst he
  have hv : c=r.val+M.weight p a := congrArg Prod.snd he
  exact ⟨s.val+M.weight p a,⟨p,s,hs,a,ha,hi,by simp [hq]⟩,by omega⟩

theorem expanded_nonempty_iff {V W : Control Q K} (h : Equivalent V W) (i : I) :
    (expanded M K V i).Nonempty ↔ (expanded M K W i).Nonempty := by
  constructor
  · rintro ⟨⟨q,c⟩,hc⟩; obtain ⟨d,hd,_⟩ := expanded_dominates M h.2 i hc; exact ⟨(q,d),hd⟩
  · rintro ⟨⟨q,c⟩,hc⟩; obtain ⟨d,hd,_⟩ := expanded_dominates M h.1 i hc; exact ⟨(q,d),hd⟩

theorem emission_order {V W : Control Q K} (h : Dominates V W) (i : I)
    (hn : (expanded M K W i).Nonempty) : emission M K V i ≤ emission M K W i := by
  obtain ⟨q,hq⟩ := emission_attained M K hn
  obtain ⟨c,hc,hle⟩ := expanded_dominates M h i hq
  exact (emission_le M K hc).trans hle

theorem emission_eq {V W : Control Q K} (h : Equivalent V W) (i : I) :
    emission M K V i = emission M K W i := by
  by_cases hw : (expanded M K W i).Nonempty
  · have hv := (expanded_nonempty_iff M h i).mpr hw
    exact Nat.le_antisymm (emission_order M h.1 i hw) (emission_order M h.2 i hv)
  · have hv : ¬ (expanded M K V i).Nonempty := by rwa [expanded_nonempty_iff M h i]
    have ev := Set.not_nonempty_iff_eq_empty.mp hv
    have ew := Set.not_nonempty_iff_eq_empty.mp hw
    simp [emission,ev,ew]

theorem next_dominates {V W : Control Q K} (h : Dominates V W) (i : I)
    (he : emission M K V i = emission M K W i) :
    Dominates (next M K V i) (next M K W i) := by
  intro q r hr
  obtain ⟨c,hc,hle⟩ := expanded_dominates M h i hr
  have hm := emission_le M K hc
  let s : Fin (K+1) := ⟨c-emission M K V i,by have := r.isLt; dsimp at hle; omega⟩
  refine ⟨s,?_,?_⟩
  · change (q,emission M K V i+s.val) ∈ expanded M K V i
    have eq : emission M K V i+s.val=c := by dsimp [s]; omega
    rwa [eq]
  · dsimp [s]; dsimp at hle; omega

theorem next_equivalent {V W : Control Q K} (h : Equivalent V W) (i : I) :
    Equivalent (next M K V i) (next M K W i) :=
  ⟨next_dominates M h.1 i (emission_eq M h i),next_dominates M h.2 i (emission_eq M h i).symm⟩

theorem final_order {V W : Control Q K} (h : Dominates V W) (hn : W.Nonempty) :
    sInf (finalCosts M K V) ≤ sInf (finalCosts M K W) := by
  have hne : (finalCosts M K W).Nonempty := by
    obtain ⟨⟨q,r⟩,hr⟩ := hn
    exact ⟨r.val+M.final q,q,r,hr,rfl⟩
  obtain ⟨q,r,hr,he⟩ := Nat.sInf_mem hne
  obtain ⟨s,hs,hle⟩ := h q r hr
  have hh : sInf (finalCosts M K V) ≤ s.val+M.final q := Nat.sInf_le ⟨q,s,hs,rfl⟩
  omega

theorem terminal_eq {V W : Control Q K} (h : Equivalent V W) :
    terminal M K V = terminal M K W := by
  classical
  by_cases hw : W.Nonempty
  · have hv := (nonempty_iff h).mpr hw
    have he := Nat.le_antisymm (final_order M h.1 hw) (final_order M h.2 hv)
    simp [terminal,hv,hw,he]
  · have hv : ¬ V.Nonempty := by rwa [nonempty_iff h]
    simp [terminal,hv,hw]

abbrev Vector (Q : Type) (K : ℕ) := Q → Option (Fin (K+1))

def decode (v : Vector Q K) : Control Q K := {p | v p.1 = some p.2}

theorem least_exists (V : Control Q K) (q : Q) (h : ∃ r, (q,r) ∈ V) :
    ∃ r, (q,r) ∈ V ∧ ∀ s, (q,s) ∈ V → r.val ≤ s.val := by
  let S : Set ℕ := {n | ∃ r, (q,r) ∈ V ∧ r.val=n}
  have hn : S.Nonempty := by obtain ⟨r,hr⟩ := h; exact ⟨r.val,r,hr,rfl⟩
  obtain ⟨r,hr,he⟩ := Nat.sInf_mem hn
  refine ⟨r,hr,?_⟩
  intro s hs
  rw [he]
  exact Nat.sInf_le ⟨s,hs,rfl⟩

noncomputable def encode (V : Control Q K) : Vector Q K := by
  classical
  exact fun q => if h : ∃ r, (q,r) ∈ V then some (Classical.choose (least_exists V q h)) else none

theorem encode_equivalent (V : Control Q K) : Equivalent (decode (encode V)) V := by
  classical
  constructor
  · intro q r hr
    have h : ∃ r, (q,r) ∈ V := ⟨r,hr⟩
    let s := Classical.choose (least_exists V q h)
    have hs := Classical.choose_spec (least_exists V q h)
    refine ⟨s,?_,hs.2 r hr⟩
    simp [decode,encode,h,s]
  · intro q r hr
    change encode V q = some r at hr
    unfold encode at hr
    split_ifs at hr with h
    · have he := Option.some.inj hr
      exact ⟨r,he ▸ (Classical.choose_spec (least_exists V q h)).1,le_rfl⟩

noncomputable def model (K : ℕ) : Subsequential.Machine I (Vector Q K) where
  start := encode (initial M K)
  step := fun v i => encode (next M K (decode v) i)
  output := fun v i => emission M K (decode v) i
  final := fun v => terminal M K (decode v)

theorem equivalent_values {V : Control Q K} {v : Vector Q K}
    (h : Equivalent (decode v) V) (us : List I) :
    (model M K).valueFrom v us = (CostApplication.model M K).valueFrom V us := by
  induction us generalizing V v with
  | nil => exact terminal_eq M h
  | cons i us ih =>
    rw [Subsequential.Machine.valueFrom,Subsequential.Machine.valueFrom]
    change ((model M K).valueFrom (encode (next M K (decode v) i)) us).map
      (emission M K (decode v) i+·) = _
    rw [ih (equivalent_trans (encode_equivalent _) (next_equivalent M h i)),emission_eq M h i]
    rfl

theorem model_value (K : ℕ) (us : List I) :
    (model M K).value us = WeightedCost.evaluate M K us := by
  rw [← CostApplication.model_value]
  exact equivalent_values M (encode_equivalent _) us

theorem vector_card [Fintype Q] [DecidableEq Q] (K : ℕ) : Fintype.card (Vector Q K) = (K+2)^Fintype.card Q := by
  simp [Vector,Fintype.card_fun]

variable {S O : Type}
open CostApplication

noncomputable def rawModel
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) (C : ℕ) :=
  DelayedWindows.compose (model (nativeMachine f del ok) (4*C))

theorem raw_model_value
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) (C : ℕ) (us : List S) :
    (rawModel f del ok C).value us = (CostApplication.rawModel f del ok C).value us := by
  rw [rawModel,CostApplication.rawModel,DelayedWindows.composed_value,
    DelayedWindows.composed_value,model_value,CostApplication.model_value]

theorem native_subsequential [Finite S] [Finite O]
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) :
    ∃ V : Type, Nonempty (Fintype V) ∧ ∃ T : Subsequential.Machine S V,
      (∀ xs, RegularProjection.nativeWinner f del ok xs →
        T.value (rawInput xs) = some (RegularProjection.nativeScore f del xs)) ∧
      (∀ us, T.value us = none ↔ ¬ feasible ok us) := by
  classical
  letI := Fintype.ofFinite S
  letI := Fintype.ofFinite O
  obtain ⟨C,hC⟩ := LocalScore.finite_local_bound f
  refine ⟨_,⟨Fintype.ofFinite _⟩,rawModel f del ok C,?_,?_⟩
  · intro xs hx
    rw [raw_model_value]
    exact CostApplication.raw_value_winner f del ok C hC hx
  · intro us
    rw [raw_model_value]
    exact CostApplication.raw_none f del ok C hC us

end CostVector
