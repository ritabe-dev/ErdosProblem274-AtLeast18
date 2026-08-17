import ErdosProblems.E274.FiberKernelDFSCertificateP1N008

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node7_unsat :
    kernelFiberDFS4 45360 [16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(22680, [6, 3]), (22680, [6, 3]), (22680, [3, 6])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_16]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_node8_unsat]

end ErdosProblems.E274
