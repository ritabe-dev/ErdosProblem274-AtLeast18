import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 3232 visited states. -/
theorem kernelFiberP2_leaf27_unsat :
    kernelFiberDFS4 30240 [16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(10080, [6, 6]), (15120, [6, 3]), (20160, [6, 6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
