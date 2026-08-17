import ErdosProblems.E274.FiberKernelDFSCertificateP3N001
import ErdosProblems.E274.FiberKernelDFSCertificateP3N015
import ErdosProblems.E274.FiberKernelDFSCertificateP3N029

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node0_unsat :
    kernelFiberDFS4 15120 [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(0, []), (0, []), (0, [])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_6]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_node1_unsat, kernelFiberP3_node15_unsat, kernelFiberP3_node29_unsat]

end ErdosProblems.E274
