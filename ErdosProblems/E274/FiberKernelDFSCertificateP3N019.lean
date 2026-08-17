import ErdosProblems.E274.FiberKernelDFSCertificateP3N020

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node19_unsat :
    kernelFiberDFS4 15120 [16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(7560, [6, 3]), (7560, [3, 6]), (7560, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_16]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_node20_unsat]

end ErdosProblems.E274
