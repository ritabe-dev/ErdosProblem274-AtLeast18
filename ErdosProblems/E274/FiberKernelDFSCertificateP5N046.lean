import ErdosProblems.E274.FiberKernelDFSCertificateP5N047
import ErdosProblems.E274.FiberKernelDFSCertificateP5B036
import ErdosProblems.E274.FiberKernelDFSCertificateP5B037
import ErdosProblems.E274.FiberKernelDFSCertificateP5B038
import ErdosProblems.E274.FiberKernelDFSCertificateP5B039
import ErdosProblems.E274.FiberKernelDFSCertificateP5B040
import ErdosProblems.E274.FiberKernelDFSCertificateP5B041

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node46_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(2520, [6]), (7560, [6, 3]), (7560, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_node47_unsat, kernelFiberP5_leaf36_unsat, kernelFiberP5_leaf37_unsat, kernelFiberP5_leaf38_unsat, kernelFiberP5_leaf39_unsat, kernelFiberP5_leaf40_unsat, kernelFiberP5_leaf41_unsat]

end ErdosProblems.E274
