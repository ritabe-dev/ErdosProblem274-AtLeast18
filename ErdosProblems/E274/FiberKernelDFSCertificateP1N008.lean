import ErdosProblems.E274.FiberKernelDFSCertificateP1B004
import ErdosProblems.E274.FiberKernelDFSCertificateP1B005
import ErdosProblems.E274.FiberKernelDFSCertificateP1B006

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node8_unsat :
    kernelFiberDFS4 45360 [18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(26460, [12, 6, 3]), (26460, [12, 6, 3]), (26460, [12, 3, 6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_leaf4_unsat, kernelFiberP1_leaf5_unsat, kernelFiberP1_leaf6_unsat]

end ErdosProblems.E274
