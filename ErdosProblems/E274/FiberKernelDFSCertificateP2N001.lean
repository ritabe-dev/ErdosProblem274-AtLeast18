import ErdosProblems.E274.FiberKernelDFSCertificateP2B000
import ErdosProblems.E274.FiberKernelDFSCertificateP2N003

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node1_unsat :
    kernelFiberDFS4 30240 [8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(10080, [3]), (10080, [3]), (0, [])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_8]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_leaf0_unsat, kernelFiberP2_node3_unsat]

end ErdosProblems.E274
