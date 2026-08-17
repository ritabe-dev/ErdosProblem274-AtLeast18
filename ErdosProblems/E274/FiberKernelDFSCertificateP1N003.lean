import ErdosProblems.E274.FiberKernelDFSCertificateP1B001
import ErdosProblems.E274.FiberKernelDFSCertificateP1B002
import ErdosProblems.E274.FiberKernelDFSCertificateP1B003
import ErdosProblems.E274.FiberKernelDFSCertificateP1N007
import ErdosProblems.E274.FiberKernelDFSCertificateP1B007
import ErdosProblems.E274.FiberKernelDFSCertificateP1B008
import ErdosProblems.E274.FiberKernelDFSCertificateP1B009

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node3_unsat :
    kernelFiberDFS4 45360 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(22680, [6, 3]), (22680, [6, 3]), (7560, [6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_leaf1_unsat, kernelFiberP1_leaf2_unsat, kernelFiberP1_leaf3_unsat, kernelFiberP1_node7_unsat, kernelFiberP1_leaf7_unsat, kernelFiberP1_leaf8_unsat, kernelFiberP1_leaf9_unsat]

end ErdosProblems.E274
