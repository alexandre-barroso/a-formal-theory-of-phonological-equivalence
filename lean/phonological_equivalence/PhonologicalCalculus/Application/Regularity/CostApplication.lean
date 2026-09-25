                   
import PhonologicalCalculus.Application.Regularity.WeightedCost
import PhonologicalCalculus.Application.Regularity.Subsequential
import PhonologicalCalculus.Application.Regularity.NativePending

namespace CostApplication
open BoundedMemory
variable {Q A I : Type} (M : Machine Q A I) (K : ℕ)

noncomputable def model : Subsequential.Machine I (WeightedCost.Control Q K) where
  start := WeightedCost.initial M K
  step := WeightedCost.next M K
  output := WeightedCost.emission M K
  final := WeightedCost.terminal M K

theorem model_execution (us : List I) :
    (model M K).execution (model M K).start us = WeightedCost.run M K us := rfl

theorem model_value (us : List I) :
    (model M K).value us = WeightedCost.evaluate M K us := by
  rw [Subsequential.Machine.value,Subsequential.Machine.valueFrom_execution,model_execution]
  rfl

theorem model_winner (hb : M.bounded K) {xs : List A} (h : M.winner xs) :
    (model M K).value (xs.map M.input) = some (M.total M.start xs) := by
  rw [model_value]
  exact WeightedCost.evaluate_winner M K hb h

theorem model_none (hb : M.bounded K) (us : List I) :
    (model M K).value us = none ↔ ¬ ∃ xs, M.valid xs ∧ xs.map M.input = us := by
  rw [model_value]
  exact WeightedCost.evaluate_none_iff M K hb us

theorem model_finite [Finite Q] : Nonempty (Fintype (WeightedCost.Control Q K)) :=
  ⟨Fintype.ofFinite _⟩

variable {S O : Type}
abbrev Z (S O : Type) := ReferenceWindows.Window S × O

def nativeMachine
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) :
    Machine (ShiftRegister.Register (Z S O)) (RegularProjection.Token S O) (ReferenceWindows.Window S) :=
  ShiftRegister.machine (LocalScore.charge f) del RegularProjection.input
    (fun t => ok (RegularProjection.input t).c (RegularProjection.output t))

def rawInput (xs : List (RegularProjection.Token S O)) : List S :=
  xs.map (fun t => (RegularProjection.input t).c)

def feasible (ok : S → Option O → Prop) (us : List S) : Prop :=
  ∃ xs : List (RegularProjection.Token S O), ReferenceWindows.valid (xs.map RegularProjection.input) ∧
    (∀ t ∈ xs, ok (RegularProjection.input t).c (RegularProjection.output t)) ∧ rawInput xs = us

@[simp] theorem native_input
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) :
    (nativeMachine f del ok).input = RegularProjection.input := rfl

theorem native_total
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop)
    (xs : List (RegularProjection.Token S O)) :
    (nativeMachine f del ok).total (nativeMachine f del ok).start xs =
      RegularProjection.nativeScore f del xs :=
  LocalScore.native_score_bridge f del RegularProjection.input _ xs

theorem native_winner
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop)
    {xs : List (RegularProjection.Token S O)} (h : RegularProjection.nativeWinner f del ok xs) :
    (nativeMachine f del ok).winner xs := by
  rcases (RegularProjection.native_winner_iff f del ok xs).mp h with ⟨_,ha,hw⟩
  refine ⟨ha,?_⟩
  intro ys hy he
  rw [native_total,native_total]
  exact hw ys hy he

theorem annotation_input {xs : List (RegularProjection.Token S O)}
    (h : ReferenceWindows.valid (xs.map RegularProjection.input)) :
    xs.map RegularProjection.input = ReferenceWindows.annotate none none (rawInput xs) := by
  simpa [rawInput,List.map_map,Function.comp_def] using (ReferenceWindows.valid_iff_canonical _).mp h

theorem feasible_iff
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) (us : List S) :
    feasible ok us ↔ ∃ xs, (nativeMachine f del ok).valid xs ∧
      xs.map (nativeMachine f del ok).input = ReferenceWindows.annotate none none us := by
  constructor
  · rintro ⟨xs,hv,ha,hu⟩
    exact ⟨xs,ha,by simpa [hu] using annotation_input hv⟩
  · rintro ⟨xs,ha,he⟩
    change xs.map RegularProjection.input = ReferenceWindows.annotate none none us at he
    refine ⟨xs,?_,ha,?_⟩
    · rw [he]; exact ReferenceWindows.annotate_valid us
    · have h := congrArg (List.map ReferenceWindows.Window.c) he
      simpa [rawInput,List.map_map,Function.comp_def,ReferenceWindows.annotate_centers] using h

theorem native_winner_exists
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop)
    {us : List S} (h : feasible ok us) :
    ∃ xs, RegularProjection.nativeWinner f del ok xs ∧ rawInput xs = us := by
  obtain ⟨xs,hv,he⟩ := (feasible_iff f del ok us).mp h
  obtain ⟨ys,hw,hy⟩ := WeightedCost.winner_exists (nativeMachine f del ok) ⟨xs,hv,he⟩
  change ys.map RegularProjection.input = ReferenceWindows.annotate none none us at hy
  refine ⟨ys,(RegularProjection.native_winner_iff f del ok ys).mpr ⟨?_,hw.1,?_⟩,?_⟩
  · rw [hy]; exact ReferenceWindows.annotate_valid us
  · intro zs hz hs
    have hh := hw.2 zs hz hs
    simpa only [native_total] using hh
  · have hh := congrArg (List.map ReferenceWindows.Window.c) hy
    simpa [rawInput,List.map_map,Function.comp_def,ReferenceWindows.annotate_centers] using hh

noncomputable def rawModel
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) (C : ℕ) :=
  DelayedWindows.compose (model (nativeMachine f del ok) (4*C))

theorem native_bounded
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop)
    (C : ℕ) (hC : ∀ z a b c d, f z a b c d ≤ C) :
    (nativeMachine f del ok).bounded (4*C) :=
  ShiftRegister.continuation_bound (LocalScore.charge f) del RegularProjection.input _ C
    (LocalScore.local_charge_bound f C hC)

theorem raw_value_winner
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop)
    (C : ℕ) (hC : ∀ z a b c d, f z a b c d ≤ C)
    {xs : List (RegularProjection.Token S O)} (h : RegularProjection.nativeWinner f del ok xs) :
    (rawModel f del ok C).value (rawInput xs) = some (RegularProjection.nativeScore f del xs) := by
  rw [rawModel,DelayedWindows.composed_value,← annotation_input h.1]
  have hres := model_winner (nativeMachine f del ok) (4*C) (native_bounded f del ok C hC)
    (native_winner f del ok h)
  simpa only [native_total,native_input] using hres

theorem raw_none
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop)
    (C : ℕ) (hC : ∀ z a b c d, f z a b c d ≤ C) (us : List S) :
    (rawModel f del ok C).value us = none ↔ ¬ feasible ok us := by
  rw [rawModel,DelayedWindows.composed_value,model_none _ _ (native_bounded f del ok C hC),feasible_iff f del ok us]

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
  exact ⟨_,⟨Fintype.ofFinite _⟩,rawModel f del ok C,
    fun _ h => raw_value_winner f del ok C hC h,raw_none f del ok C hC⟩

end CostApplication
