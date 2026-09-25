import PhonologicalOpacity.Attenuation.Typology.Region00
import PhonologicalOpacity.Attenuation.Typology.Region01
import PhonologicalOpacity.Attenuation.Typology.Region02
import PhonologicalOpacity.Attenuation.Typology.Region03
import PhonologicalOpacity.Attenuation.Typology.Region04
import PhonologicalOpacity.Attenuation.Typology.Region05
import PhonologicalOpacity.Attenuation.Typology.Region06
import PhonologicalOpacity.Attenuation.Typology.Region07
import PhonologicalOpacity.Attenuation.Typology.Region08
import PhonologicalOpacity.Attenuation.Typology.Region09
import PhonologicalOpacity.Attenuation.Typology.Region10
import PhonologicalOpacity.Attenuation.Typology.Region11
import PhonologicalOpacity.Attenuation.Typology.Region12
import PhonologicalOpacity.Attenuation.Typology.Region13
import PhonologicalOpacity.Attenuation.Typology.Region14
import PhonologicalOpacity.Attenuation.Typology.Region15
import PhonologicalOpacity.Attenuation.Typology.Region16
import PhonologicalOpacity.Attenuation.Typology.Region17
import PhonologicalOpacity.Attenuation.Typology.Region18
import PhonologicalOpacity.Attenuation.Typology.Region19
import PhonologicalOpacity.Attenuation.Typology.Region20
import PhonologicalOpacity.Attenuation.Typology.Region21
import PhonologicalOpacity.Attenuation.Typology.Region22
import PhonologicalOpacity.Attenuation.Typology.Region23
import PhonologicalOpacity.Attenuation.Typology.Region24
import PhonologicalOpacity.Attenuation.Typology.Region25
import PhonologicalOpacity.Attenuation.Typology.Region26
import PhonologicalOpacity.Attenuation.Typology.Region27
import PhonologicalOpacity.Attenuation.Typology.Region28
import PhonologicalOpacity.Attenuation.Typology.Region29
import PhonologicalOpacity.Attenuation.Typology.Region30
import PhonologicalOpacity.Attenuation.Typology.Region31
import PhonologicalOpacity.Attenuation.Typology.Region32
import PhonologicalOpacity.Attenuation.Typology.Region33
import PhonologicalOpacity.Attenuation.Typology.Region34
import PhonologicalOpacity.Attenuation.Typology.Region35
import PhonologicalOpacity.Attenuation.Typology.Region36
import PhonologicalOpacity.Attenuation.Typology.Region37
import PhonologicalOpacity.Attenuation.Typology.Region38
import PhonologicalOpacity.Attenuation.Typology.Region39
import PhonologicalOpacity.Attenuation.Typology.Region40
import PhonologicalOpacity.Attenuation.Typology.Region41
import PhonologicalOpacity.Attenuation.Typology.Region42
import PhonologicalOpacity.Attenuation.Typology.Region43
import PhonologicalOpacity.Attenuation.Typology.Region44
import PhonologicalOpacity.Attenuation.Typology.Region45
import PhonologicalOpacity.Attenuation.Typology.Region46
import PhonologicalOpacity.Attenuation.Typology.Domain
import PhonologicalOpacity.Attenuation.Typology.Bounds
import Mathlib.Tactic.IntervalCases
namespace InteractionTypology
def Region (index : Nat) (l : ℝ) : Prop := match index with
  | 0 => l < 1
  | 1 => l < 1
  | 2 => False
  | 3 => 0 < l
  | 4 => False
  | 5 => True
  | 6 => True
  | 7 => False
  | 8 => False
  | 9 => False
  | 10 => False
  | 11 => True
  | 12 => True
  | 13 => False
  | 14 => True
  | 15 => False
  | 16 => True
  | 17 => True
  | 18 => False
  | 19 => False
  | 20 => 0 < 1-2*l-l^2
  | 21 => l < 1/2
  | 22 => False
  | 23 => False
  | 24 => 0 < l ∧ l < 1/2
  | 25 => 0 < 1-2*l^2
  | 26 => False
  | 27 => True
  | 28 => False
  | 29 => False
  | 30 => False
  | 31 => False
  | 32 => True
  | 33 => False
  | 34 => l < 1/2
  | 35 => 0 < l
  | 36 => False
  | 37 => True
  | 38 => True
  | 39 => False
  | 40 => l < 1
  | 41 => False
  | 42 => True
  | 43 => False
  | 44 => False
  | 45 => False
  | 46 => True
  | _ => False
theorem exact_regions (a : Assignment) (ha : a∈assignments) (l : ℝ) (hl : 0≤l) (hu : l≤1) :
    (∃w,Nonnegative w ∧ FullSelection patterns[a.pattern]! a.modes a.subject w l) ↔ Region a.system l := by
  simp only [full_iff_systems,source_system a ha]
  have hi : a.system<47 := by simpa [allSystems] using (assignment_arities a ha).2.1
  interval_cases h : a.system <;> simp only [Region,allSystems,List.getElem!_cons_zero,List.getElem!_cons_succ]
  all_goals first
    | exact region0 l hl hu
    | exact region1 l hl hu
    | exact region2 l hl hu
    | exact region3 l hl hu
    | exact region4 l hl hu
    | exact region5 l hl hu
    | exact region6 l hl hu
    | exact region7 l hl hu
    | exact region8 l hl hu
    | exact region9 l hl hu
    | exact region10 l hl hu
    | exact region11 l hl hu
    | exact region12 l hl hu
    | exact region13 l hl hu
    | exact region14 l hl hu
    | exact region15 l hl hu
    | exact region16 l hl hu
    | exact region17 l hl hu
    | exact region18 l hl hu
    | exact region19 l hl hu
    | exact region20 l hl hu
    | exact region21 l hl hu
    | exact region22 l hl hu
    | exact region23 l hl hu
    | exact region24 l hl hu
    | exact region25 l hl hu
    | exact region26 l hl hu
    | exact region27 l hl hu
    | exact region28 l hl hu
    | exact region29 l hl hu
    | exact region30 l hl hu
    | exact region31 l hl hu
    | exact region32 l hl hu
    | exact region33 l hl hu
    | exact region34 l hl hu
    | exact region35 l hl hu
    | exact region36 l hl hu
    | exact region37 l hl hu
    | exact region38 l hl hu
    | exact region39 l hl hu
    | exact region40 l hl hu
    | exact region41 l hl hu
    | exact region42 l hl hu
    | exact region43 l hl hu
    | exact region44 l hl hu
    | exact region45 l hl hu
    | exact region46 l hl hu
end InteractionTypology
