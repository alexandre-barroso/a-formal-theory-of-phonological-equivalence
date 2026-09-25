import PhonologicalOpacity.Gua.Select.G34a
import PhonologicalOpacity.Gua.Select.G34b
import PhonologicalOpacity.Gua.Select.N7
import PhonologicalOpacity.Gua.Select.G37c
import PhonologicalOpacity.Gua.Select.C24ei
import PhonologicalOpacity.Gua.Export
import Lean
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  let mut theorems : Nat := 0
  let projectModules := #["PhonologicalOpacity.Gua.Reader","PhonologicalOpacity.Gua.Core","PhonologicalOpacity.Gua.Select.G34a","PhonologicalOpacity.Gua.Select.G34b","PhonologicalOpacity.Gua.Select.N7","PhonologicalOpacity.Gua.Select.G37c","PhonologicalOpacity.Gua.Select.C24ei","PhonologicalOpacity.Gua.Export"]
  for (n,info) in env.constants.toList do
    let isProject := match env.getModuleIdxFor? n with
      | none => true
      | some idx =>
        let modName := env.header.moduleNames[idx.toNat]!.toString
        projectModules.contains modName || modName == "PhonologicalOpacity.Gua.BlockBridge" || modName.startsWith "PhonologicalOpacity.Gua.Blocks."
    if isProject then
      count := count + 1
      if n.toString.startsWith "_private" then privateCount := privateCount + 1
      match info with
      | .axiomInfo _ => throwError "Project axiom: {n}"
      | .thmInfo _ => theorems := theorems + 1
      | _ => pure ()
      let axs ← collectAxioms n
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unapproved axiom {ax} in {n}"
      logInfo m!"AUDIT {n}: {axs}"
  logInfo m!"PASS full project census: {count} constants, {privateCount} private, {theorems} theorem constants"
