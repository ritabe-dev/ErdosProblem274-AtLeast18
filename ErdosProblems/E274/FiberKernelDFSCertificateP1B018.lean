import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 2969 visited states. -/
theorem kernelFiberP1_leaf18_unsat :
    kernelFiberDFS4 45360 [16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(22680, [6, 3]), (15120, [6, 6]), (30240, [6, 6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
