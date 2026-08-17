import ErdosProblems.E274.FiberKernelDFSCertificateP4B005
import ErdosProblems.E274.FiberKernelDFSCertificateP4B006
import ErdosProblems.E274.FiberKernelDFSCertificateP4B007
import ErdosProblems.E274.FiberKernelDFSCertificateP4N012
import ErdosProblems.E274.FiberKernelDFSCertificateP4B011
import ErdosProblems.E274.FiberKernelDFSCertificateP4B012
import ErdosProblems.E274.FiberKernelDFSCertificateP4B013

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP4_node8_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(7560, [6, 3]), (7560, [6, 3]), (2520, [6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP4_leaf5_unsat, kernelFiberP4_leaf6_unsat, kernelFiberP4_leaf7_unsat, kernelFiberP4_node12_unsat, kernelFiberP4_leaf11_unsat, kernelFiberP4_leaf12_unsat, kernelFiberP4_leaf13_unsat]

end ErdosProblems.E274
