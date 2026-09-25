import PhonologicalCalculus.All
open Lean in
run_cmd do
  let env ← getEnv
  let mut modules : Array Name := #[]
  for modName in env.header.moduleNames do
    if (`PhonologicalCalculus).isPrefixOf modName && modName != `PhonologicalCalculus.Audit then
      modules := modules.push modName
  let mut theorems : Nat := 0
  let mut constants : Nat := 0
  let mut used : Std.HashSet Name := {}
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        constants := constants + 1
        match info with
        | .axiomInfo _ => throwError m!"Project axiom {name}"
        | .thmInfo _ =>
          theorems := theorems + 1
          let axs ← collectAxioms name
          for ax in axs do
            used := used.insert ax
            unless [`propext, `Classical.choice, `Quot.sound].contains ax do
              throwError m!"Disallowed axiom {ax} in {name}"
        | _ => pure ()
  logInfo m!"MODULE_AUDIT theorems={theorems} constants={constants} modules={modules.size} axioms={used.toList}"
