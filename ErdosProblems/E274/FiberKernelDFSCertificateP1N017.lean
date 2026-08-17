import ErdosProblems.E274.FiberKernelDFSCertificateP1B011
import ErdosProblems.E274.FiberKernelDFSCertificateP1N019
import ErdosProblems.E274.FiberKernelDFSCertificateP1B015
import ErdosProblems.E274.FiberKernelDFSCertificateP1B016
import ErdosProblems.E274.FiberKernelDFSCertificateP1B017
import ErdosProblems.E274.FiberKernelDFSCertificateP1B018
import ErdosProblems.E274.FiberKernelDFSCertificateP1B019

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node17_unsat :
    kernelFiberDFS4 45360 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(22680, [6, 3]), (7560, [6]), (22680, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_leaf11_unsat, kernelFiberP1_node19_unsat, kernelFiberP1_leaf15_unsat, kernelFiberP1_leaf16_unsat, kernelFiberP1_leaf17_unsat, kernelFiberP1_leaf18_unsat, kernelFiberP1_leaf19_unsat]

end ErdosProblems.E274
