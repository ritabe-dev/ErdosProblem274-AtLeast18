import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 4365 visited states. -/
theorem kernelFiberP4_leaf23_unsat :
    kernelFiberDFS4 15120 [16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(10080, [6, 6, 3]), (5040, [6, 6]), (7560, [6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
