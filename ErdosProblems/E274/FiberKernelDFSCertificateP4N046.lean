import ErdosProblems.E274.FiberKernelDFSCertificateP4N047
import ErdosProblems.E274.FiberKernelDFSCertificateP4B036
import ErdosProblems.E274.FiberKernelDFSCertificateP4B037
import ErdosProblems.E274.FiberKernelDFSCertificateP4B038
import ErdosProblems.E274.FiberKernelDFSCertificateP4B039
import ErdosProblems.E274.FiberKernelDFSCertificateP4B040
import ErdosProblems.E274.FiberKernelDFSCertificateP4B041

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP4_node46_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(2520, [6]), (7560, [6, 3]), (7560, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP4_node47_unsat, kernelFiberP4_leaf36_unsat, kernelFiberP4_leaf37_unsat, kernelFiberP4_leaf38_unsat, kernelFiberP4_leaf39_unsat, kernelFiberP4_leaf40_unsat, kernelFiberP4_leaf41_unsat]

end ErdosProblems.E274
