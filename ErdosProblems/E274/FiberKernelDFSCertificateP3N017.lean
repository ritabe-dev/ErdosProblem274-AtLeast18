import ErdosProblems.E274.FiberKernelDFSCertificateP3B011
import ErdosProblems.E274.FiberKernelDFSCertificateP3N019
import ErdosProblems.E274.FiberKernelDFSCertificateP3B015
import ErdosProblems.E274.FiberKernelDFSCertificateP3B016
import ErdosProblems.E274.FiberKernelDFSCertificateP3B017
import ErdosProblems.E274.FiberKernelDFSCertificateP3B018
import ErdosProblems.E274.FiberKernelDFSCertificateP3B019

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node17_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(7560, [6, 3]), (2520, [6]), (7560, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_leaf11_unsat, kernelFiberP3_node19_unsat, kernelFiberP3_leaf15_unsat, kernelFiberP3_leaf16_unsat, kernelFiberP3_leaf17_unsat, kernelFiberP3_leaf18_unsat, kernelFiberP3_leaf19_unsat]

end ErdosProblems.E274
