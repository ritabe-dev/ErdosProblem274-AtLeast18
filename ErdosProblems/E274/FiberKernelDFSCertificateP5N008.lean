import ErdosProblems.E274.FiberKernelDFSCertificateP5B005
import ErdosProblems.E274.FiberKernelDFSCertificateP5B006
import ErdosProblems.E274.FiberKernelDFSCertificateP5B007
import ErdosProblems.E274.FiberKernelDFSCertificateP5N012
import ErdosProblems.E274.FiberKernelDFSCertificateP5B011
import ErdosProblems.E274.FiberKernelDFSCertificateP5B012
import ErdosProblems.E274.FiberKernelDFSCertificateP5B013

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node8_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(7560, [6, 3]), (7560, [6, 3]), (2520, [6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_leaf5_unsat, kernelFiberP5_leaf6_unsat, kernelFiberP5_leaf7_unsat, kernelFiberP5_node12_unsat, kernelFiberP5_leaf11_unsat, kernelFiberP5_leaf12_unsat, kernelFiberP5_leaf13_unsat]

end ErdosProblems.E274
