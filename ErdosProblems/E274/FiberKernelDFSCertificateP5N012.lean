import ErdosProblems.E274.FiberKernelDFSCertificateP5N013

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
theorem kernelFiberP5_node12_unsat :
    kernelFiberDFS4 15120 [16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
      [(7560, [6, 3]), (7560, [6, 3]), (7560, [3, 6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_16]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, Nat.odd_iff, kernelFiberP5_node13_unsat]

end ErdosProblems.E274
