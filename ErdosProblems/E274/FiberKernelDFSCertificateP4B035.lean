import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 4483 visited states. -/
theorem kernelFiberP4_leaf35_unsat :
    kernelFiberDFS4 15120 [24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(8820, [12, 3, 6]), (10500, [9, 12, 6, 3]), (10500, [9, 12, 6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
