import ErdosProblems.E274.FiberKernelDFSCertificateP1B012
import ErdosProblems.E274.FiberKernelDFSCertificateP1B013
import ErdosProblems.E274.FiberKernelDFSCertificateP1B014

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node20_unsat :
    kernelFiberDFS4 45360 [18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(26460, [12, 6, 3]), (26460, [12, 3, 6]), (26460, [12, 6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_leaf12_unsat, kernelFiberP1_leaf13_unsat, kernelFiberP1_leaf14_unsat]

end ErdosProblems.E274
