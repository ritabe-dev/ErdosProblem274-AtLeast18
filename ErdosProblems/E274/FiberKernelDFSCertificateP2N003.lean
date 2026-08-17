import ErdosProblems.E274.FiberKernelDFSCertificateP2B001
import ErdosProblems.E274.FiberKernelDFSCertificateP2B002
import ErdosProblems.E274.FiberKernelDFSCertificateP2B003
import ErdosProblems.E274.FiberKernelDFSCertificateP2N007
import ErdosProblems.E274.FiberKernelDFSCertificateP2B007
import ErdosProblems.E274.FiberKernelDFSCertificateP2B008
import ErdosProblems.E274.FiberKernelDFSCertificateP2B009

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node3_unsat :
    kernelFiberDFS4 30240 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(15120, [6, 3]), (15120, [6, 3]), (5040, [6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_leaf1_unsat, kernelFiberP2_leaf2_unsat, kernelFiberP2_leaf3_unsat, kernelFiberP2_node7_unsat, kernelFiberP2_leaf7_unsat, kernelFiberP2_leaf8_unsat, kernelFiberP2_leaf9_unsat]

end ErdosProblems.E274
