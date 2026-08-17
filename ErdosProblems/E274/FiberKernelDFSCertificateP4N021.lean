import ErdosProblems.E274.FiberKernelDFSCertificateP4B014
import ErdosProblems.E274.FiberKernelDFSCertificateP4B015
import ErdosProblems.E274.FiberKernelDFSCertificateP4B016
import ErdosProblems.E274.FiberKernelDFSCertificateP4B017
import ErdosProblems.E274.FiberKernelDFSCertificateP4B018

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP4_node21_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(5040, [3]), (7560, [2]), (5040, [3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP4_leaf14_unsat, kernelFiberP4_leaf15_unsat, kernelFiberP4_leaf16_unsat, kernelFiberP4_leaf17_unsat, kernelFiberP4_leaf18_unsat]

end ErdosProblems.E274
