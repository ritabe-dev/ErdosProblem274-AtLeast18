import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 1715 visited states. -/
theorem kernelFiberP1_leaf29_unsat :
    kernelFiberDFS4 45360 [16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(12600, [9, 6]), (27720, [9, 6, 3]), (27720, [9, 6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
