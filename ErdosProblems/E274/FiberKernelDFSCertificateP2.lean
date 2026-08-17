import ErdosProblems.E274.FiberKernelDFSCertificateP2N000

/-! Generated endpoint of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

theorem kernelFiberProfile2_unsat :
    kernelFiberDFS4 fiberProfile2Scale fiberProfile2Rows
      emptyKernelFiberState = false := by
  simpa [fiberProfile2Scale, fiberProfile2Rows,
    emptyKernelFiberState] using kernelFiberP2_node0_unsat

end ErdosProblems.E274
