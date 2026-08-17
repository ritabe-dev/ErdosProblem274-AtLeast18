import ErdosProblems.E274.FiberKernelDFSCertificateP1B020
import ErdosProblems.E274.FiberKernelDFSCertificateP1N031

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node29_unsat :
    kernelFiberDFS4 45360 [8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(0, []), (15120, [3]), (15120, [3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_8]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_leaf20_unsat, kernelFiberP1_node31_unsat]

end ErdosProblems.E274
