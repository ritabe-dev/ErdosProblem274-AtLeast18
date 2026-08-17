import ErdosProblems.E274.FiberKernelDFSCertificateP1B000
import ErdosProblems.E274.FiberKernelDFSCertificateP1N003

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node1_unsat :
    kernelFiberDFS4 45360 [8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(15120, [3]), (15120, [3]), (0, [])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_8]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_leaf0_unsat, kernelFiberP1_node3_unsat]

end ErdosProblems.E274
