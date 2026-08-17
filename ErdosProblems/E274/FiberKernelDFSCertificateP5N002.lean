import ErdosProblems.E274.FiberKernelDFSCertificateP5B000
import ErdosProblems.E274.FiberKernelDFSCertificateP5B001
import ErdosProblems.E274.FiberKernelDFSCertificateP5B002
import ErdosProblems.E274.FiberKernelDFSCertificateP5B003
import ErdosProblems.E274.FiberKernelDFSCertificateP5B004

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node2_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(5040, [3]), (5040, [3]), (7560, [2])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_leaf0_unsat, kernelFiberP5_leaf1_unsat, kernelFiberP5_leaf2_unsat, kernelFiberP5_leaf3_unsat, kernelFiberP5_leaf4_unsat]

end ErdosProblems.E274
