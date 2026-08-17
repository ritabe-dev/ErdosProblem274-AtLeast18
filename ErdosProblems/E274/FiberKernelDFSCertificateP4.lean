import ErdosProblems.E274.FiberKernelDFSCertificateP4N000

/-! Generated endpoint of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

theorem kernelFiberProfile4_unsat :
    kernelFiberDFS4 fiberProfile4Scale fiberProfile4Rows
      emptyKernelFiberState = false := by
  simpa [fiberProfile4Scale, fiberProfile4Rows,
    emptyKernelFiberState] using kernelFiberP4_node0_unsat

end ErdosProblems.E274
