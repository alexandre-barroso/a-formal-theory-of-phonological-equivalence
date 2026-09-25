import PhonologicalOpacity.Attenuation.FreeWeights.Core
namespace FreeWeights
open Retained Deletion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block_N700 : checkBlock n7 ⟨1,0,0⟩ [82] 0 = true := by decide +kernel
end FreeWeights
