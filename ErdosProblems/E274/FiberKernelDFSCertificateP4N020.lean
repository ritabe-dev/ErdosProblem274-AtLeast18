import ErdosProblems.E274.FiberKernelDFSCertificateP4N021
import ErdosProblems.E274.FiberKernelDFSCertificateP4N027

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP4_node20_unsat :
    kernelFiberDFS4 15120 [8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
      [(5040, [3]), (0, []), (5040, [3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_8]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP4_node21_unsat, kernelFiberP4_node27_unsat]

end ErdosProblems.E274
