import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 1651 visited states. -/
theorem kernelFiberP2_leaf9_unsat :
    kernelFiberDFS4 30240 [16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(18480, [9, 6, 3]), (18480, [9, 6, 3]), (8400, [9, 6])] = false := by
  decide +kernel

end ErdosProblems.E274
