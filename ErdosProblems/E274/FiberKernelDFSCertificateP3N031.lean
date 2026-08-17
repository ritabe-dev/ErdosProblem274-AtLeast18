import ErdosProblems.E274.FiberKernelDFSCertificateP3N032
import ErdosProblems.E274.FiberKernelDFSCertificateP3B024
import ErdosProblems.E274.FiberKernelDFSCertificateP3B025
import ErdosProblems.E274.FiberKernelDFSCertificateP3B026
import ErdosProblems.E274.FiberKernelDFSCertificateP3B027
import ErdosProblems.E274.FiberKernelDFSCertificateP3B028
import ErdosProblems.E274.FiberKernelDFSCertificateP3B029

/-! Generated internal node of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem kernelFiberP3_node31_unsat :
    kernelFiberDFS4 15120 [12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
      [(2520, [6]), (7560, [6, 3]), (7560, [6, 3])] = false := by
  rw [kernelFiberDFS4, kernelFiberChoices4_12]
  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn, kernelFiberP3_node32_unsat, kernelFiberP3_leaf24_unsat, kernelFiberP3_leaf25_unsat, kernelFiberP3_leaf26_unsat, kernelFiberP3_leaf27_unsat, kernelFiberP3_leaf28_unsat, kernelFiberP3_leaf29_unsat]

end ErdosProblems.E274
