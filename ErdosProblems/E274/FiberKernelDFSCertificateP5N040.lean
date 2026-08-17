import ErdosProblems.E274.FiberKernelDFSCertificateP5B028
import ErdosProblems.E274.FiberKernelDFSCertificateP5B029
import ErdosProblems.E274.FiberKernelDFSCertificateP5B030
import ErdosProblems.E274.FiberKernelDFSCertificateP5B031
import ErdosProblems.E274.FiberKernelDFSCertificateP5B032

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node40_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(7560, [2]), (5040, [3]), (5040, [3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_leaf28_unsat, kernelFiberP5_leaf29_unsat, kernelFiberP5_leaf30_unsat, kernelFiberP5_leaf31_unsat, kernelFiberP5_leaf32_unsat]

end ErdosProblems.E274
