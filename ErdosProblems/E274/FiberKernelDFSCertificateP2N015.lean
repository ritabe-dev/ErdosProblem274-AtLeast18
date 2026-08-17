import ErdosProblems.E274.FiberKernelDFSCertificateP2B010
import ErdosProblems.E274.FiberKernelDFSCertificateP2N017

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node15_unsat :
    kernelFiberDFS4 30240 [8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(10080, [3]), (0, []), (10080, [3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_8]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_leaf10_unsat, kernelFiberP2_node17_unsat]

end ErdosProblems.E274
