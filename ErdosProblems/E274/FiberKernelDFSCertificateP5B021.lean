import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 4299 visited states. -/
theorem kernelFiberP5_leaf21_unsat :
    kernelFiberDFS4 15120 [24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(10500, [9, 12, 6, 3]), (8820, [12, 3, 6]), (10500, [9, 12, 6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
