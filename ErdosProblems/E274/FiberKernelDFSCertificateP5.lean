import ErdosProblems.E274.FiberKernelDFSCertificateP5N000

/-! Generated endpoint of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

theorem kernelFiberProfile5_unsat :
    kernelFiberDFS4 fiberProfile5Scale fiberProfile5Rows
      emptyKernelFiberState = false := by
  simpa [fiberProfile5Scale, fiberProfile5Rows,
    emptyKernelFiberState] using kernelFiberP5_node0_unsat

end ErdosProblems.E274
