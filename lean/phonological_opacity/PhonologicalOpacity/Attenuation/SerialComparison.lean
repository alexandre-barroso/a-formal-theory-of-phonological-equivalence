import PhonologicalOpacity.Attenuation.MutualCounterfeeding
namespace SerialComparison
open MutualCounterfeedingRegion
def applyAt (s : State) (i : Nat) (syn : Bool) : State :=
  if (reader s i syn (false,false)).1 then s.set i none else s
def pass (s : State) (syn : Bool) : State :=
  (List.range s.length).map fun i => if (reader s i syn (false,false)).1 then none else s[i]!
def onePass (s : State) (synFirst : Bool) : State := pass (pass s synFirst) (!synFirst)
def block (s : State) (rightToLeft synFirst : Bool) : State :=
  let ns := if rightToLeft then (List.range s.length).reverse else List.range s.length
  ns.foldl (fun c i => applyAt (applyAt c i synFirst) i (!synFirst)) s
theorem one_pass_exclusion (synFirst : Bool) :
    ¬ (∀ p ∈ paradigm, surface (onePass (initial p.1) synFirst) = p.2) := by
  cases synFirst <;> decide +kernel
theorem directional_block_exclusion (rightToLeft synFirst : Bool) :
    ¬ (∀ p ∈ paradigm, surface (block (initial p.1) rightToLeft synFirst) = p.2) := by
  cases rightToLeft <;> cases synFirst <;> decide +kernel
def finalDeleteAt (s : State) (i : Nat) (vowel : Bool) : State :=
  let target := if vowel then 'V' else 'C'
  if s[i]! == some target && (right s i).isEmpty then s.set i none else s
def finalBlock (s : State) (vowelFirst : Bool) : State :=
  (List.range s.length).foldl
    (fun c i => finalDeleteAt (finalDeleteAt c i vowelFirst) i (!vowelFirst)) s
theorem final_deletion_block (vowelFirst : Bool) :
    surface (finalBlock (initial "CVC") vowelFirst) = "CV" ∧
    surface (finalBlock (initial "CVCV") vowelFirst) = "CVC" := by
  cases vowelFirst <;> decide +kernel
end SerialComparison
