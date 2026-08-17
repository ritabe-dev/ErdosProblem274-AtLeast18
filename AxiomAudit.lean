import ErdosProblems.E274.FiberKernelAssignmentObstruction
import ErdosProblems.E274.LocalMargolisSchnabelFacts
import ErdosProblems.E274.UnconditionalTheorem

/-!
Release axiom audit for the closed E274 bounded theorem.

The final theorem has no external theorem argument.  Each printed endpoint is
required by `scripts/check_axiom_output.py` to use only ordinary Lean axioms.
-/

#check ErdosProblems.E274.checked_seventeen_survivors
#print axioms ErdosProblems.E274.checked_seventeen_survivors

#check ErdosProblems.E274.localMargolisSchnabelFacts
#print axioms ErdosProblems.E274.localMargolisSchnabelFacts

#check ErdosProblems.E274.kernelFiberDFS4_complete_of_orderedAssignment
#print axioms ErdosProblems.E274.kernelFiberDFS4_complete_of_orderedAssignment

#check ErdosProblems.E274.seventeenIndexFourAssignmentObstruction_kernel
#print axioms ErdosProblems.E274.seventeenIndexFourAssignmentObstruction_kernel

#check ErdosProblems.E274.erdos274AtMostSeventeen
#print axioms ErdosProblems.E274.erdos274AtMostSeventeen
