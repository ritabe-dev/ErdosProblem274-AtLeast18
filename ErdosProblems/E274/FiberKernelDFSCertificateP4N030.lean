import ErdosProblems.E274.FiberKernelDFSCertificateP4B020
import ErdosProblems.E274.FiberKernelDFSCertificateP4B021
import ErdosProblems.E274.FiberKernelDFSCertificateP4B022

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP4_node30_unsat :
    kernelFiberDFS4 15120 [18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(8820, [12, 6, 3]), (8820, [12, 3, 6]), (8820, [12, 6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP4_leaf20_unsat, kernelFiberP4_leaf21_unsat, kernelFiberP4_leaf22_unsat]

end ErdosProblems.E274
