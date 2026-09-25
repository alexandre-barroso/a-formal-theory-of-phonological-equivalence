import PhonologicalOpacity.Gua.Deletion.Core
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block_OR38_0_8 : checkBlock or38 0 [1261] 172 8 = true := by decide +kernel
#print axioms block_OR38_0_8
theorem block_OR38_1_8 : checkBlock or38 1 [1267] 12 8 = true := by decide +kernel
#print axioms block_OR38_1_8
theorem block_OR38_2_8 : checkBlock or38 2 [1332] 20 8 = true := by decide +kernel
#print axioms block_OR38_2_8
end Deletion
