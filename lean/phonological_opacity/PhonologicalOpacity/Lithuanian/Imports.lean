import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    let path ← findOLean modName
    logInfo m!"MODULE_IMPORT {modName} PATH {path}"
