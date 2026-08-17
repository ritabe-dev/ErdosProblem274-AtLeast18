import ErdosProblems.E274.FiberKernelDFSCertificateP1N000

/-! Generated endpoint of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

theorem kernelFiberProfile1_unsat :
    kernelFiberDFS4 fiberProfile1Scale fiberProfile1Rows
      emptyKernelFiberState = false := by
  simpa [fiberProfile1Scale, fiberProfile1Rows,
    emptyKernelFiberState] using kernelFiberP1_node0_unsat

end ErdosProblems.E274
