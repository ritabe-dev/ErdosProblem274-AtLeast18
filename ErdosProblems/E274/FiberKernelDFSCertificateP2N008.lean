import ErdosProblems.E274.FiberKernelDFSCertificateP2B004
import ErdosProblems.E274.FiberKernelDFSCertificateP2B005
import ErdosProblems.E274.FiberKernelDFSCertificateP2B006

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node8_unsat :
    kernelFiberDFS4 30240 [18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(17640, [12, 6, 3]), (17640, [12, 6, 3]), (17640, [12, 3, 6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_leaf4_unsat, kernelFiberP2_leaf5_unsat, kernelFiberP2_leaf6_unsat]

end ErdosProblems.E274
