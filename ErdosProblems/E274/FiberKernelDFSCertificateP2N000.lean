import ErdosProblems.E274.FiberKernelDFSCertificateP2N001
import ErdosProblems.E274.FiberKernelDFSCertificateP2N015
import ErdosProblems.E274.FiberKernelDFSCertificateP2N029

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node0_unsat :
    kernelFiberDFS4 30240 [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(0, []), (0, []), (0, [])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_6]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_node1_unsat, kernelFiberP2_node15_unsat, kernelFiberP2_node29_unsat]

end ErdosProblems.E274
