import ErdosProblems.E274.FiberKernelDFSCertificateP5N040
import ErdosProblems.E274.FiberKernelDFSCertificateP5N046

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node39_unsat :
    kernelFiberDFS4 15120 [8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(0, []), (5040, [3]), (5040, [3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_8]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_node40_unsat, kernelFiberP5_node46_unsat]

end ErdosProblems.E274
