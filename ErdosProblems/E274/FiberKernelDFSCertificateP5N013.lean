import ErdosProblems.E274.FiberKernelDFSCertificateP5B008
import ErdosProblems.E274.FiberKernelDFSCertificateP5B009
import ErdosProblems.E274.FiberKernelDFSCertificateP5B010

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node13_unsat :
    kernelFiberDFS4 15120 [18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(8820, [12, 6, 3]), (8820, [12, 6, 3]), (8820, [12, 3, 6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_18]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_leaf8_unsat, kernelFiberP5_leaf9_unsat, kernelFiberP5_leaf10_unsat]

end ErdosProblems.E274
