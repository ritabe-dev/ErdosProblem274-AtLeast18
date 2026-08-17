import ErdosProblems.E274.FiberKernelDFSCertificateP1
import ErdosProblems.E274.FiberKernelDFSCertificateP2
import ErdosProblems.E274.FiberKernelDFSCertificateP3
import ErdosProblems.E274.FiberKernelDFSCertificateP4
import ErdosProblems.E274.FiberKernelDFSCertificateP5
import ErdosProblems.E274.FiberKernelDFSSoundness
import ErdosProblems.E274.KernelFiberComposition

/-!
# Kernel-certified obstruction for the five E274 profiles

The arithmetic search leaves exactly five length-seventeen profiles.  This
module combines the direct assignment-to-DFS completeness theorem with the
five split, kernel-reduced negative DFS certificates.  It closes the single
finite interface required by `KernelFiberComposition`.
-/

namespace ErdosProblems.E274

/-- A closed negative DFS result contradicts any declarative assignment on
the corresponding index-four profile. -/
theorem noIndexFourAssignment_of_kernelFiberDFS_unsat
    {rows : List Nat} {scale : Nat} (hnodup : rows.Nodup)
    (hfour : 4 ∉ rows) (hscale : kernelFiberScale4 rows = scale)
    (hunsat : kernelFiberDFS4 scale rows emptyKernelFiberState = false) :
    IndexFourFiberAssignment (4 :: rows) → False := by
  intro assignment
  have htrue := assignment.kernelFiberDFS4_true hnodup hfour
  rw [hscale, hunsat] at htrue
  cases htrue

theorem kernelFiberScale4_profile1 :
    kernelFiberScale4 fiberProfile1Rows = fiberProfile1Scale := by
  decide +kernel

theorem kernelFiberScale4_profile2 :
    kernelFiberScale4 fiberProfile2Rows = fiberProfile2Scale := by
  decide +kernel

theorem kernelFiberScale4_profile3 :
    kernelFiberScale4 fiberProfile3Rows = fiberProfile3Scale := by
  decide +kernel

theorem kernelFiberScale4_profile4 :
    kernelFiberScale4 fiberProfile4Rows = fiberProfile4Scale := by
  decide +kernel

theorem kernelFiberScale4_profile5 :
    kernelFiberScale4 fiberProfile5Rows = fiberProfile5Scale := by
  decide +kernel

/-- None of the five exact length-seventeen arithmetic survivors admits the
declarative three-fiber assignment forced by a genuine coset partition. -/
theorem seventeenIndexFourAssignmentObstruction_kernel :
    SeventeenIndexFourAssignmentObstruction := by
  intro xs hmem assignment
  simp only [seventeenSurvivors, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · change IndexFourFiberAssignment (4 :: fiberProfile1Rows) at assignment
    exact noIndexFourAssignment_of_kernelFiberDFS_unsat
      (by decide +kernel) (by decide +kernel)
      kernelFiberScale4_profile1 kernelFiberProfile1_unsat assignment
  · change IndexFourFiberAssignment (4 :: fiberProfile2Rows) at assignment
    exact noIndexFourAssignment_of_kernelFiberDFS_unsat
      (by decide +kernel) (by decide +kernel)
      kernelFiberScale4_profile2 kernelFiberProfile2_unsat assignment
  · change IndexFourFiberAssignment (4 :: fiberProfile3Rows) at assignment
    exact noIndexFourAssignment_of_kernelFiberDFS_unsat
      (by decide +kernel) (by decide +kernel)
      kernelFiberScale4_profile3 kernelFiberProfile3_unsat assignment
  · change IndexFourFiberAssignment (4 :: fiberProfile4Rows) at assignment
    exact noIndexFourAssignment_of_kernelFiberDFS_unsat
      (by decide +kernel) (by decide +kernel)
      kernelFiberScale4_profile4 kernelFiberProfile4_unsat assignment
  · change IndexFourFiberAssignment (4 :: fiberProfile5Rows) at assignment
    exact noIndexFourAssignment_of_kernelFiberDFS_unsat
      (by decide +kernel) (by decide +kernel)
      kernelFiberScale4_profile5 kernelFiberProfile5_unsat assignment

end ErdosProblems.E274
