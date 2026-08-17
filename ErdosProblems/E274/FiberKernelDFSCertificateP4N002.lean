import ErdosProblems.E274.FiberKernelDFSCertificateP4B000
import ErdosProblems.E274.FiberKernelDFSCertificateP4B001
import ErdosProblems.E274.FiberKernelDFSCertificateP4B002
import ErdosProblems.E274.FiberKernelDFSCertificateP4B003
import ErdosProblems.E274.FiberKernelDFSCertificateP4B004

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP4_node2_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(5040, [3]), (5040, [3]), (7560, [2])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP4_leaf0_unsat, kernelFiberP4_leaf1_unsat, kernelFiberP4_leaf2_unsat, kernelFiberP4_leaf3_unsat, kernelFiberP4_leaf4_unsat]

end ErdosProblems.E274
