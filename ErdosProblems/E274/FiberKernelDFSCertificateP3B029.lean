import ErdosProblems.E274.FiberKernelDFSProfileData

/-! Generated kernel certificate branch; do not edit by hand. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation rejects a DFS subtree of 1681 visited states. -/
theorem kernelFiberP3_leaf29_unsat :
    kernelFiberDFS4 15120 [16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(4200, [9, 6]), (9240, [9, 6, 3]), (9240, [9, 6, 3])] = false := by
  decide +kernel

end ErdosProblems.E274
