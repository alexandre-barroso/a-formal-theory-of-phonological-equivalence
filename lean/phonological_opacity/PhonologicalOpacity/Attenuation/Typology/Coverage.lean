import PhonologicalOpacity.Attenuation.Typology.Complete
namespace InteractionTypology
def modeVectors : Nat → List (List Mode)
  | 0 => [[]]
  | n+1 => [(true,true),(false,false),(true,false),(false,true)].flatMap
      fun m => (modeVectors n).map (m :: ·)
theorem mode_vectors_complete (n : Nat) (ms : List Mode) :
    ms∈modeVectors n ↔ ms.length=n := by
  induction n generalizing ms with
  | zero => simp [modeVectors]
  | succ n ih =>
    cases ms with
    | nil => simp [modeVectors]
    | cons m ms =>
      rcases m with ⟨a,b⟩
      cases a <;> cases b <;> simp [modeVectors,ih]
def lookup (i : Nat) (ms : List Mode) (sub : Bool) : Assignment :=
  (assignments.find? fun a => a.pattern==i && a.modes==ms && a.subject==sub).getD ⟨0,[],false,0⟩
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lookup_certificate : ∀i∈List.range patterns.length,
    ∀ms∈modeVectors patterns[i]!.rules.length,∀sub∈[false,true],
      lookup i ms sub∈assignments ∧ (lookup i ms sub).pattern=i ∧
      (lookup i ms sub).modes=ms ∧ (lookup i ms sub).subject=sub := by decide +kernel
theorem lookup_valid (i : Nat) (hi : i<patterns.length) (ms : List Mode)
    (hm : ms.length=patterns[i]!.rules.length) (sub : Bool) :
    lookup i ms sub∈assignments ∧ (lookup i ms sub).pattern=i ∧
      (lookup i ms sub).modes=ms ∧ (lookup i ms sub).subject=sub := by
  exact lookup_certificate i (by simpa using hi) ms ((mode_vectors_complete _ _).mpr hm) sub (by cases sub <;> simp)
theorem all_modes_exact (i : Nat) (hi : i<patterns.length) (ms : List Mode)
    (hm : ms.length=patterns[i]!.rules.length) (sub : Bool) (l : ℝ) (hl : 0≤l) (hu : l≤1) :
    (∃w,Nonnegative w ∧ FullSelection patterns[i]! ms sub w l) ↔
      Region (lookup i ms sub).system l := by
  obtain ⟨ha,hp,hm,hs⟩ := lookup_valid i hi ms hm sub
  simpa [hp,hm,hs] using exact_regions (lookup i ms sub) ha l hl hu
end InteractionTypology
