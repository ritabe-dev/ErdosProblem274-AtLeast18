import ErdosProblems.E274.FiberKernelDFSCertificateP5B019
import ErdosProblems.E274.FiberKernelDFSCertificateP5N029
import ErdosProblems.E274.FiberKernelDFSCertificateP5B023
import ErdosProblems.E274.FiberKernelDFSCertificateP5B024
import ErdosProblems.E274.FiberKernelDFSCertificateP5B025
import ErdosProblems.E274.FiberKernelDFSCertificateP5B026
import ErdosProblems.E274.FiberKernelDFSCertificateP5B027

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node27_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(7560, [6, 3]), (2520, [6]), (7560, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_leaf19_unsat, kernelFiberP5_node29_unsat, kernelFiberP5_leaf23_unsat, kernelFiberP5_leaf24_unsat, kernelFiberP5_leaf25_unsat, kernelFiberP5_leaf26_unsat, kernelFiberP5_leaf27_unsat]

end ErdosProblems.E274
