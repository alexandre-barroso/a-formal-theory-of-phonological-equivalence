                  
                   
import PhonologicalCalculus.Application.Regularity.Irrational.Grammar

namespace NativeIrrational

def partialValueFrom {Q : Type} (next : Q → Bool → Q) (weight : Q → Bool → ℝ)
    (finish : Q → Option ℝ) : Q → List Bool → Option ℝ
  | q, [] => finish q
  | q, x::xs => (partialValueFrom next weight finish (next q x) xs).map (weight q x + ·)

noncomputable def totalized {Q : Type} (q : Q) (next : Q → Bool → Q)
    (weight : Q → Bool → ℝ) (finish : Q → Option ℝ) : WeightedMachine Q where
  initial := q
  transition := next
  weight := weight
  finalWeight := fun q => (finish q).getD 0
  initialWeight := 0

theorem totalized_emission_independent {Q : Type} (a b q : Q) (next : Q → Bool → Q)
    (weight : Q → Bool → ℝ) (finish : Q → Option ℝ) (u : List Bool) :
    (totalized a next weight finish).emission q u = (totalized b next weight finish).emission q u := by
  induction u generalizing q with
  | nil => rfl
  | cons x u ih =>
    simp only [WeightedMachine.emission]
    exact congrArg (weight q x + ·) (ih (next q x))

theorem partial_value_eq {Q : Type} (q : Q) (next : Q → Bool → Q)
    (weight : Q → Bool → ℝ) (finish : Q → Option ℝ) (u : List Bool) :
    partialValueFrom next weight finish q u =
      (finish (u.foldl next q)).map ((totalized q next weight finish).emission q u + ·) := by
  induction u generalizing q with
  | nil => simp [partialValueFrom,WeightedMachine.emission]
  | cons x u ih =>
    simp only [partialValueFrom,List.foldl_cons,ih,Option.map_map,WeightedMachine.emission,totalized]
    congr 1
    funext v
    simp only [Function.comp_def,add_assoc]
    congr 1
    exact congrArg (· + v) (totalized_emission_independent (next q x) q (next q x) next weight finish u)

theorem no_finite_partial_weighted_machine {Q : Type} [Finite Q] (q : Q)
    (next : Q → Bool → Q) (weight : Q → Bool → ℝ) (finish : Q → Option ℝ) :
    ¬ (∀ u, partialValueFrom next weight finish q u = some (minimum u)) := by
  intro h
  apply no_finite_weighted_machine (totalized q next weight finish)
  intro u
  have hu := h u
  rw [partial_value_eq] at hu
  cases he : finish (u.foldl next q) with
  | none => simp [he] at hu
  | some r =>
    simp only [he,Option.map_some,Option.some.injEq] at hu
    simpa only [WeightedMachine.value,totalized,WeightedMachine.state,he,Option.getD_some,zero_add] using hu
end NativeIrrational
