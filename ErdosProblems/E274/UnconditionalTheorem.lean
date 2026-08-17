import ErdosProblems.E274.FiberKernelAssignmentObstruction

/-!
# Unconditional Lean endpoint for the E274 bounded theorem

This module closes the public endpoint without an external theorem parameter.
The six source-shaped Margolis--Schnabel consequences are proved locally, the
seventeen-term arithmetic boundary is certified by split kernel reductions,
and the five remaining profiles are rejected by the split kernel DFS
certificates.  The unrestricted Herzog--Schönheim conjecture is not asserted.
-/

namespace ErdosProblems.E274

universe u

/-- Every exact finite coset partition of an arbitrary group into between two
and seventeen cells contains two cells whose subgroup indices agree.

Equivalently, any counterexample to the unrestricted Herzog--Schönheim
conjecture would require at least eighteen cells. -/
theorem erdos274AtMostSeventeen : erdos274AtMostSeventeenTarget.{u} :=
  erdos274AtMostSeventeen_of_assignmentObstruction
    seventeenIndexFourAssignmentObstruction_kernel

end ErdosProblems.E274
