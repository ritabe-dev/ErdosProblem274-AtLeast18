import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 5267 visited states. -/
theorem kernelFiberP2_leaf0_unsat :
    kernelFiberDFS4 30240 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(10080, [3]), (10080, [3]), (15120, [2])] = false := by
  decide +kernel

end ErdosProblems.E274
