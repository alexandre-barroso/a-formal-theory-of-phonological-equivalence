import PhonologicalOpacity.Gua.Deletion.Core
namespace Deletion
open Retained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block_C21b_0_0 : checkBlock c21 0 [117] 160 0 = true := by decide +kernel
#print axioms block_C21b_0_0
theorem block_C21b_1_0 : checkBlock c21 1 [122] 0 0 = true := by decide +kernel
#print axioms block_C21b_1_0
theorem block_C21b_2_0 : checkBlock c21 2 [18,44,96,128,161] 16 0 = true := by decide +kernel
#print axioms block_C21b_2_0
end Deletion
