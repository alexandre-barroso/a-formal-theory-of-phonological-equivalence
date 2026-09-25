import PhonologicalOpacity.Gua.Deletion.Core
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block_OR38_0_3 : checkBlock or38 0 [1261] 172 3 = true := by decide +kernel
#print axioms block_OR38_0_3
theorem block_OR38_1_3 : checkBlock or38 1 [1267] 12 3 = true := by decide +kernel
#print axioms block_OR38_1_3
theorem block_OR38_2_3 : checkBlock or38 2 [1332] 20 3 = true := by decide +kernel
#print axioms block_OR38_2_3
end Deletion
