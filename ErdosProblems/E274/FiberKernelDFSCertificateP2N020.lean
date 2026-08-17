import ErdosProblems.E274.FiberKernelDFSCertificateP2B012
import ErdosProblems.E274.FiberKernelDFSCertificateP2B013
import ErdosProblems.E274.FiberKernelDFSCertificateP2B014

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node20_unsat :
    kernelFiberDFS4 30240 [18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(17640, [12, 6, 3]), (17640, [12, 3, 6]), (17640, [12, 6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_leaf12_unsat, kernelFiberP2_leaf13_unsat, kernelFiberP2_leaf14_unsat]

end ErdosProblems.E274
