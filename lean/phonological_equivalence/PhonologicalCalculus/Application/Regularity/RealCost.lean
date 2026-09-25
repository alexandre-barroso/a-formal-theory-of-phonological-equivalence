                   
import PhonologicalCalculus.Application.Regularity.CostVector
import PhonologicalCalculus.Application.Regularity.LatticeScore

namespace RealSubsequential

structure Machine (I Q : Type) where
  start : Q
  step : Q → I → Q
  output : Q → I → ℝ
  final : Q → Option ℝ

namespace Machine
variable {I Q : Type} (T : Machine I Q)
def valueFrom : Q → List I → Option ℝ
  | q, [] => T.final q
  | q, i :: us => (valueFrom (T.step q i) us).map (T.output q i + ·)
def value (us : List I) : Option ℝ := T.valueFrom T.start us
end Machine

variable {I Q : Type}
def scale (δ : ℝ) (T : Subsequential.Machine I Q) : Machine I Q where
  start := T.start
  step := T.step
  output := fun q i => δ * T.output q i
  final := fun q => (T.final q).map (fun n => δ * n)

theorem scale_valueFrom (δ : ℝ) (T : Subsequential.Machine I Q) (q : Q) (us : List I) :
    (scale δ T).valueFrom q us = (T.valueFrom q us).map (fun n => δ*n) := by
  induction us generalizing q with
  | nil => rfl
  | cons i us ih =>
    rw [Machine.valueFrom,Subsequential.Machine.valueFrom]
    change ((scale δ T).valueFrom (T.step q i) us).map (δ * T.output q i + ·) = _
    rw [ih]
    cases T.valueFrom (T.step q i) us <;> simp [Nat.cast_add,mul_add]

theorem scale_value (δ : ℝ) (T : Subsequential.Machine I Q) (us : List I) :
    (scale δ T).value us = (T.value us).map (fun n => δ*n) :=
  scale_valueFrom δ T T.start us

end RealSubsequential

namespace CostApplication
variable {S O : Type}

theorem real_native_subsequential [Finite S] [Finite O]
    (f : Z S O → Option (Z S O) → Option (Z S O) → Option (Z S O) → Option (Z S O) → ℝ)
    (del : ReferenceWindows.Window S → ℝ) (ok : S → Option O → Prop)
    (δ : ℝ) (hδ : 0 < δ)
    (hf : ∀ z a b c d, ∃ n : ℕ, f z a b c d = δ*n)
    (hd : ∀ d, ∃ n : ℕ, del d = δ*n) :
    ∃ V : Type, Nonempty (Fintype V) ∧ ∃ T : RealSubsequential.Machine S V,
      (∀ xs, LatticeScore.nativeWinner f del ok xs →
        T.value (rawInput xs) = some (LatticeScore.nativeScore f del xs)) ∧
      (∀ us, T.value us = none ↔ ¬ feasible ok us) := by
  classical
  choose g hg using hf
  choose dd hdd using hd
  have hscore (xs : List (RegularProjection.Token S O)) :
      LatticeScore.nativeScore f del xs = δ * RegularProjection.nativeScore g dd xs := by
    rw [LatticeScore.nativeScore,LatticeScore.delete_scale δ del dd hdd,
      LatticeScore.objective_scale δ f g hg]
    simp [RegularProjection.nativeScore,Nat.cast_add,mul_add]
  have hw (xs : List (RegularProjection.Token S O)) :
      LatticeScore.nativeWinner f del ok xs ↔ RegularProjection.nativeWinner g dd ok xs := by
    simp only [LatticeScore.nativeWinner,RegularProjection.nativeWinner,hscore,
      LocalScore.positive_scaling_order δ hδ]
  obtain ⟨V,hV,T,ht,hn⟩ := CostVector.native_subsequential g dd ok
  refine ⟨V,hV,RealSubsequential.scale δ T,?_,?_⟩
  · intro xs hx
    rw [RealSubsequential.scale_value,ht xs ((hw xs).mp hx)]
    simp [hscore]
  · intro us
    rw [RealSubsequential.scale_value,← hn us]
    cases T.value us <;> simp

end CostApplication
