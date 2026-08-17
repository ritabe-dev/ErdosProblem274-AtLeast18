import ErdosProblems.E274.FiberKernelDFSCertificateP1N001
import ErdosProblems.E274.FiberKernelDFSCertificateP1N015
import ErdosProblems.E274.FiberKernelDFSCertificateP1N029

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node0_unsat :
    kernelFiberDFS4 45360 [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(0, []), (0, []), (0, [])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_6]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_node1_unsat, kernelFiberP1_node15_unsat, kernelFiberP1_node29_unsat]

end ErdosProblems.E274
