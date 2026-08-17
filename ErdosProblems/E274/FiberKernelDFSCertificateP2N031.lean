import ErdosProblems.E274.FiberKernelDFSCertificateP2N032
import ErdosProblems.E274.FiberKernelDFSCertificateP2B024
import ErdosProblems.E274.FiberKernelDFSCertificateP2B025
import ErdosProblems.E274.FiberKernelDFSCertificateP2B026
import ErdosProblems.E274.FiberKernelDFSCertificateP2B027
import ErdosProblems.E274.FiberKernelDFSCertificateP2B028
import ErdosProblems.E274.FiberKernelDFSCertificateP2B029

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP2_node31_unsat :
    kernelFiberDFS4 30240 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
      [(5040, [6]), (15120, [6, 3]), (15120, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP2_node32_unsat, kernelFiberP2_leaf24_unsat, kernelFiberP2_leaf25_unsat, kernelFiberP2_leaf26_unsat, kernelFiberP2_leaf27_unsat, kernelFiberP2_leaf28_unsat, kernelFiberP2_leaf29_unsat]

end ErdosProblems.E274
