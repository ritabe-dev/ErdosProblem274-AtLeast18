import ErdosProblems.E274.FiberKernelDFSCertificateP2B011
import ErdosProblems.E274.FiberKernelDFSCertificateP2N019
import ErdosProblems.E274.FiberKernelDFSCertificateP2B015
import ErdosProblems.E274.FiberKernelDFSCertificateP2B016
import ErdosProblems.E274.FiberKernelDFSCertificateP2B017
import ErdosProblems.E274.FiberKernelDFSCertificateP2B018
import ErdosProblems.E274.FiberKernelDFSCertificateP2B019

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node17_unsat :
    kernelFiberDFS4 30240 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(15120, [6, 3]), (5040, [6]), (15120, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_leaf11_unsat, kernelFiberP2_node19_unsat, kernelFiberP2_leaf15_unsat, kernelFiberP2_leaf16_unsat, kernelFiberP2_leaf17_unsat, kernelFiberP2_leaf18_unsat, kernelFiberP2_leaf19_unsat]

end ErdosProblems.E274
