import ErdosProblems.E274.FiberKernelDFSCertificateP3B004
import ErdosProblems.E274.FiberKernelDFSCertificateP3B005
import ErdosProblems.E274.FiberKernelDFSCertificateP3B006

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node8_unsat :
    kernelFiberDFS4 15120 [18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(8820, [12, 6, 3]), (8820, [12, 6, 3]), (8820, [12, 3, 6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_leaf4_unsat, kernelFiberP3_leaf5_unsat, kernelFiberP3_leaf6_unsat]

end ErdosProblems.E274
