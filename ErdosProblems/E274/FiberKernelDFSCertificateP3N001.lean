import ErdosProblems.E274.FiberKernelDFSCertificateP3B000
import ErdosProblems.E274.FiberKernelDFSCertificateP3N003

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node1_unsat :
    kernelFiberDFS4 15120 [8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(5040, [3]), (5040, [3]), (0, [])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_8]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_leaf0_unsat, kernelFiberP3_node3_unsat]

end ErdosProblems.E274
