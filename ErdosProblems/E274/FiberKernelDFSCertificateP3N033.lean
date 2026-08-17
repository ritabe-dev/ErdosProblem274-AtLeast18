import ErdosProblems.E274.FiberKernelDFSCertificateP3B021
import ErdosProblems.E274.FiberKernelDFSCertificateP3B022
import ErdosProblems.E274.FiberKernelDFSCertificateP3B023

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node33_unsat :
    kernelFiberDFS4 15120 [18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(8820, [12, 3, 6]), (8820, [12, 6, 3]), (8820, [12, 6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_leaf21_unsat, kernelFiberP3_leaf22_unsat, kernelFiberP3_leaf23_unsat]

end ErdosProblems.E274
