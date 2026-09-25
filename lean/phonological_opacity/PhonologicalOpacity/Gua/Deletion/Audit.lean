import PhonologicalOpacity.Gua.Deletion.Core
import PhonologicalOpacity.Gua.Deletion.Bindings
import PhonologicalOpacity.Gua.Deletion.Bound
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3800
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3801
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3802
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3803
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3804
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3805
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3806
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3807
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3808
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3809
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3810
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3811
import PhonologicalOpacity.Gua.Deletion.Blocks.OR3812
import PhonologicalOpacity.Gua.Deletion.Select.OR38
import PhonologicalOpacity.Gua.Deletion.Blocks.C21b00
import PhonologicalOpacity.Gua.Deletion.Select.C21b
import PhonologicalOpacity.Gua.Deletion.Blocks.C23UE00
import PhonologicalOpacity.Gua.Deletion.Select.C23UE
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a00
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a01
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a02
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a03
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a04
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a05
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a06
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a07
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a08
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a09
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a10
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a11
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a12
import PhonologicalOpacity.Gua.Deletion.Select.D0G34a
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b00
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b01
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b02
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b03
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b04
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b05
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b06
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b07
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b08
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b09
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b10
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b11
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b12
import PhonologicalOpacity.Gua.Deletion.Select.D0G34b
import PhonologicalOpacity.Gua.Deletion.Blocks.D0N700
import PhonologicalOpacity.Gua.Deletion.Select.D0N7
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c00
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c01
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c02
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c03
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c04
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c05
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c06
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c07
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c08
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c09
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c10
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c11
import PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c12
import PhonologicalOpacity.Gua.Deletion.Select.D0G37c
import PhonologicalOpacity.Gua.Deletion.Blocks.D0C2400
import PhonologicalOpacity.Gua.Deletion.Select.D0C24
import PhonologicalOpacity.Gua.Deletion.Baseline
import PhonologicalOpacity.Gua.Deletion.Export
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let projectModules : Array Name := #[`PhonologicalOpacity.Gua.Reader,`PhonologicalOpacity.Gua.Core,`PhonologicalOpacity.Gua.BlockBridge,`PhonologicalOpacity.Gua.Select.G34a,`PhonologicalOpacity.Gua.Select.G34b,`PhonologicalOpacity.Gua.Select.N7,`PhonologicalOpacity.Gua.Select.G37c,`PhonologicalOpacity.Gua.Select.C24ei,`PhonologicalOpacity.Gua.Blocks.G34a00,`PhonologicalOpacity.Gua.Blocks.G34a01,`PhonologicalOpacity.Gua.Blocks.G34a02,`PhonologicalOpacity.Gua.Blocks.G34a03,`PhonologicalOpacity.Gua.Blocks.G34a04,`PhonologicalOpacity.Gua.Blocks.G34a05,`PhonologicalOpacity.Gua.Blocks.G34a06,`PhonologicalOpacity.Gua.Blocks.G34a07,`PhonologicalOpacity.Gua.Blocks.G34a08,`PhonologicalOpacity.Gua.Blocks.G34a09,`PhonologicalOpacity.Gua.Blocks.G34a10,`PhonologicalOpacity.Gua.Blocks.G34a11,`PhonologicalOpacity.Gua.Blocks.G34a12,`PhonologicalOpacity.Gua.Blocks.G34b00,`PhonologicalOpacity.Gua.Blocks.G34b01,`PhonologicalOpacity.Gua.Blocks.G34b02,`PhonologicalOpacity.Gua.Blocks.G34b03,`PhonologicalOpacity.Gua.Blocks.G34b04,`PhonologicalOpacity.Gua.Blocks.G34b05,`PhonologicalOpacity.Gua.Blocks.G34b06,`PhonologicalOpacity.Gua.Blocks.G34b07,`PhonologicalOpacity.Gua.Blocks.G34b08,`PhonologicalOpacity.Gua.Blocks.G34b09,`PhonologicalOpacity.Gua.Blocks.G34b10,`PhonologicalOpacity.Gua.Blocks.G34b11,`PhonologicalOpacity.Gua.Blocks.G34b12,`PhonologicalOpacity.Gua.Blocks.G37c00,`PhonologicalOpacity.Gua.Blocks.G37c01,`PhonologicalOpacity.Gua.Blocks.G37c02,`PhonologicalOpacity.Gua.Blocks.G37c03,`PhonologicalOpacity.Gua.Blocks.G37c04,`PhonologicalOpacity.Gua.Blocks.G37c05,`PhonologicalOpacity.Gua.Blocks.G37c06,`PhonologicalOpacity.Gua.Blocks.G37c07,`PhonologicalOpacity.Gua.Blocks.G37c08,`PhonologicalOpacity.Gua.Blocks.G37c09,`PhonologicalOpacity.Gua.Blocks.G37c10,`PhonologicalOpacity.Gua.Blocks.G37c11,`PhonologicalOpacity.Gua.Blocks.G37c12,`PhonologicalOpacity.Gua.Deletion.Core,`PhonologicalOpacity.Gua.Deletion.Bindings,`PhonologicalOpacity.Gua.Deletion.Bound,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3800,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3801,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3802,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3803,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3804,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3805,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3806,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3807,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3808,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3809,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3810,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3811,`PhonologicalOpacity.Gua.Deletion.Blocks.OR3812,`PhonologicalOpacity.Gua.Deletion.Select.OR38,`PhonologicalOpacity.Gua.Deletion.Blocks.C21b00,`PhonologicalOpacity.Gua.Deletion.Select.C21b,`PhonologicalOpacity.Gua.Deletion.Blocks.C23UE00,`PhonologicalOpacity.Gua.Deletion.Select.C23UE,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a00,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a01,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a02,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a03,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a04,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a05,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a06,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a07,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a08,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a09,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a10,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a11,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34a12,`PhonologicalOpacity.Gua.Deletion.Select.D0G34a,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b00,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b01,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b02,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b03,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b04,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b05,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b06,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b07,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b08,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b09,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b10,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b11,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G34b12,`PhonologicalOpacity.Gua.Deletion.Select.D0G34b,`PhonologicalOpacity.Gua.Deletion.Blocks.D0N700,`PhonologicalOpacity.Gua.Deletion.Select.D0N7,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c00,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c01,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c02,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c03,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c04,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c05,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c06,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c07,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c08,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c09,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c10,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c11,`PhonologicalOpacity.Gua.Deletion.Blocks.D0G37c12,`PhonologicalOpacity.Gua.Deletion.Select.D0G37c,`PhonologicalOpacity.Gua.Deletion.Blocks.D0C2400,`PhonologicalOpacity.Gua.Deletion.Select.D0C24,`PhonologicalOpacity.Gua.Deletion.Baseline,`PhonologicalOpacity.Gua.Deletion.Export]
  for modName in env.header.moduleNames do
    let path ← findOLean modName
    logInfo m!"MODULE_IMPORT {modName} PATH {path}"
  let mut count : Nat := 0
  for (name,info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if projectModules.contains modName then
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
