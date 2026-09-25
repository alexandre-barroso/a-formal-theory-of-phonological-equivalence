import PhonologicalGrounding
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for modName in env.header.moduleNames do
    if (`PhonologicalGrounding).isPrefixOf modName && modName != `PhonologicalGrounding.Audit then
      modules := modules.push modName
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if modules.contains modName then
        count := count + 1
        match info with
        | .axiomInfo _ => throwError m!"Project axiom {name}"
        | _ =>
          let axs ← collectAxioms name
          logInfo m!"MODULE_CONSTANT {name} MODULE {modName} AXIOMS {axs}"
          for ax in axs do
            unless [`propext, `Classical.choice, `Quot.sound].contains ax do
              throwError m!"Disallowed axiom {ax} in {name}"
  logInfo m!"MODULE_AUDITED_CONSTANTS={count} MODULES={modules.size}"
