import ErdosProblems.E274.FiberKernelDFSCertificateP5B014
import ErdosProblems.E274.FiberKernelDFSCertificateP5B015
import ErdosProblems.E274.FiberKernelDFSCertificateP5B016
import ErdosProblems.E274.FiberKernelDFSCertificateP5B017
import ErdosProblems.E274.FiberKernelDFSCertificateP5B018

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node21_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(5040, [3]), (7560, [2]), (5040, [3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_leaf14_unsat, kernelFiberP5_leaf15_unsat, kernelFiberP5_leaf16_unsat, kernelFiberP5_leaf17_unsat, kernelFiberP5_leaf18_unsat]

end ErdosProblems.E274
