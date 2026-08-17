import ErdosProblems.E274.FiberKernelDFSCertificateP1N032
import ErdosProblems.E274.FiberKernelDFSCertificateP1B024
import ErdosProblems.E274.FiberKernelDFSCertificateP1B025
import ErdosProblems.E274.FiberKernelDFSCertificateP1B026
import ErdosProblems.E274.FiberKernelDFSCertificateP1B027
import ErdosProblems.E274.FiberKernelDFSCertificateP1B028
import ErdosProblems.E274.FiberKernelDFSCertificateP1B029

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP1_node31_unsat :
    kernelFiberDFS4 45360 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
      [(7560, [6]), (22680, [6, 3]), (22680, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP1_node32_unsat, kernelFiberP1_leaf24_unsat, kernelFiberP1_leaf25_unsat, kernelFiberP1_leaf26_unsat, kernelFiberP1_leaf27_unsat, kernelFiberP1_leaf28_unsat, kernelFiberP1_leaf29_unsat]

end ErdosProblems.E274
