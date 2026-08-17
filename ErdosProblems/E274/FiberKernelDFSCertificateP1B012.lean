import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 3120 visited states. -/
theorem kernelFiberP1_leaf12_unsat :
    kernelFiberDFS4 45360 [24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(31500, [9, 12, 6, 3]), (31500, [9, 12, 3, 6]), (26460, [12, 6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
