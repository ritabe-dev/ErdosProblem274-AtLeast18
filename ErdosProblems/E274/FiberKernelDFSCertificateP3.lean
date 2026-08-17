import ErdosProblems.E274.FiberKernelDFSCertificateP3N000

/-! Generated endpoint of the split kernel DFS certificate. -/

namespace ErdosProblems.E274

theorem kernelFiberProfile3_unsat :
    kernelFiberDFS4 fiberProfile3Scale fiberProfile3Rows
      emptyKernelFiberState = false := by
  simpa [fiberProfile3Scale, fiberProfile3Rows,
    emptyKernelFiberState] using kernelFiberP3_node0_unsat

end ErdosProblems.E274
