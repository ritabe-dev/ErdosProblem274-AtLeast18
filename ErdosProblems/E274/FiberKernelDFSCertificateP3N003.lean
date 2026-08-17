import ErdosProblems.E274.FiberKernelDFSCertificateP3B001
import ErdosProblems.E274.FiberKernelDFSCertificateP3B002
import ErdosProblems.E274.FiberKernelDFSCertificateP3B003
import ErdosProblems.E274.FiberKernelDFSCertificateP3N007
import ErdosProblems.E274.FiberKernelDFSCertificateP3B007
import ErdosProblems.E274.FiberKernelDFSCertificateP3B008
import ErdosProblems.E274.FiberKernelDFSCertificateP3B009

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node3_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(7560, [6, 3]), (7560, [6, 3]), (2520, [6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_leaf1_unsat, kernelFiberP3_leaf2_unsat, kernelFiberP3_leaf3_unsat, kernelFiberP3_node7_unsat, kernelFiberP3_leaf7_unsat, kernelFiberP3_leaf8_unsat, kernelFiberP3_leaf9_unsat]

end ErdosProblems.E274
