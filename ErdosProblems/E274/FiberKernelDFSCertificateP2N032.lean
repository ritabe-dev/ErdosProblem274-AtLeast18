import ErdosProblems.E274.FiberKernelDFSCertificateP2N033

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node32_unsat :
    kernelFiberDFS4 30240 [16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(15120, [3, 6]), (15120, [6, 3]), (15120, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_16]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_node33_unsat]

end ErdosProblems.E274
