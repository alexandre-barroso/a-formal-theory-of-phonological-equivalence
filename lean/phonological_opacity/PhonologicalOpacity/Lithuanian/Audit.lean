import PhonologicalOpacity.Lithuanian.Imports
import PhonologicalOpacity.Lithuanian.Core
import PhonologicalOpacity.Lithuanian.Proofs
import PhonologicalOpacity.Lithuanian.Export
open Lean in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`PhonologicalOpacity.Lithuanian.Imports,`PhonologicalOpacity.Lithuanian.Core,`PhonologicalOpacity.Lithuanian.Proofs,`PhonologicalOpacity.Lithuanian.Export]
  for modName in env.header.moduleNames do
    let path ← findOLean modName
    logInfo m!"MODULE_IMPORT {modName} PATH {path}"
  let mut count : Nat := 0
  for (name,info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if modules.contains modName then
        count := count+1
        match info with
        | .axiomInfo _ => throwError m!"Project axiom {name}"
        | _ =>
          let axs ← collectAxioms name
          logInfo m!"MODULE_CONSTANT {name} MODULE {modName} AXIOMS {axs}"
          for ax in axs do
            unless [`propext,`Classical.choice,`Quot.sound].contains ax do
              throwError m!"Disallowed axiom {ax} in {name}"
  logInfo m!"MODULE_AUDITED_CONSTANTS={count}"
