import PhonologicalOpacity.Attenuation.Typology.Data
namespace InteractionTypology
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem named_columns : ∀p∈patterns,p.names.length≤9 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem assignment_arities : ∀a∈assignments,
    a.pattern<patterns.length ∧ a.system<allSystems.length ∧
    a.modes.length=patterns[a.pattern]!.rules.length := by decide +kernel
def choices (p : Pattern) (x : Option String) : List (Option String) :=
  ((p.options.find? fun a => some a.1==x).map Prod.snd).getD [x]
def Admissible (p : Pattern) (original candidate : State) : Prop :=
  List.Forall₂ (fun x y => y∈choices p x) original candidate
theorem generator_complete (p : Pattern) (original candidate : State) :
    candidate∈generate p original ↔ Admissible p original candidate := by
  induction original generalizing candidate with
  | nil => cases candidate <;> simp [generate,Admissible]
  | cons x xs ih =>
    cases candidate with
    | nil => simp [generate,Admissible]
    | cons y ys =>
      simp only [generate,List.mem_flatMap,List.mem_map,List.cons.injEq]
      simp [Admissible,choices]
      intro hy
      simpa [Admissible,choices] using ih ys
end InteractionTypology
