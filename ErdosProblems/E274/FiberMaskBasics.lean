import ErdosProblems.E274.IndexFourFiberBridge

/-!
# Lightweight support-mask facts for the E274 index-four bridge

This module is deliberately independent of the executable breadth-first fiber
search.  It encodes a nonempty subset of the three non-anchor boxes by a
three-bit natural-number mask and records the exact membership and cardinality
facts needed by a kernel-only finite certificate.
-/

namespace ErdosProblems.E274

/-- Decode the low three bits of a natural number as a subset of the three
labelled non-anchor boxes. -/
def kernelDecodedSupport3 (mask : Nat) : Finset (Fin 3) :=
  Finset.univ.filter fun column => mask.testBit column

/-- The number of selected boxes in a three-bit support mask. -/
def kernelSupportSize3 (mask : Nat) : Nat :=
  (kernelDecodedSupport3 mask).card

/-- Encode a concrete support as a three-bit natural-number mask. -/
def kernelMaskOfSupport3 (support : Finset (Fin 3)) : Nat :=
  (if (0 : Fin 3) ∈ support then 1 else 0) +
  (if (1 : Fin 3) ∈ support then 2 else 0) +
  (if (2 : Fin 3) ∈ support then 4 else 0)

@[simp] theorem testBit_kernelMaskOfSupport3
    (support : Finset (Fin 3)) (b : Fin 3) :
    (kernelMaskOfSupport3 support).testBit b = decide (b ∈ support) := by
  classical
  fin_cases b <;>
    simp only [kernelMaskOfSupport3, Fin.isValue, Nat.testBit]
  all_goals
    split_ifs <;> simp_all

@[simp] theorem mem_kernelDecodedSupport3_kernelMaskOfSupport3
    (support : Finset (Fin 3)) (b : Fin 3) :
    b ∈ kernelDecodedSupport3 (kernelMaskOfSupport3 support) ↔ b ∈ support := by
  classical
  simp [kernelDecodedSupport3, testBit_kernelMaskOfSupport3]

@[simp] theorem kernelDecodedSupport3_kernelMaskOfSupport3
    (support : Finset (Fin 3)) :
    kernelDecodedSupport3 (kernelMaskOfSupport3 support) = support := by
  classical
  ext b
  simp

@[simp] theorem kernelSupportSize3_kernelMaskOfSupport3
    (support : Finset (Fin 3)) :
    kernelSupportSize3 (kernelMaskOfSupport3 support) = support.card := by
  simp [kernelSupportSize3]

theorem kernelMaskOfSupport3_pos {support : Finset (Fin 3)}
    (hsupport : support.Nonempty) : 1 ≤ kernelMaskOfSupport3 support := by
  classical
  rcases hsupport with ⟨b, hb⟩
  fin_cases b <;> simp_all [kernelMaskOfSupport3] <;>
    split_ifs <;> omega

theorem kernelMaskOfSupport3_lt_eight (support : Finset (Fin 3)) :
    kernelMaskOfSupport3 support < 8 := by
  classical
  simp only [kernelMaskOfSupport3]
  split_ifs <;> omega

/-- The support mask attached directly to a declarative fiber assignment. -/
def IndexFourFiberAssignment.kernelMask {xs : List Nat}
    (assignment : IndexFourFiberAssignment xs) (i : IndexFourFiberRow xs) : Nat :=
  kernelMaskOfSupport3 (assignment.support i)

theorem IndexFourFiberAssignment.kernelMask_pos {xs : List Nat}
    (assignment : IndexFourFiberAssignment xs) (i : IndexFourFiberRow xs) :
    1 ≤ assignment.kernelMask i :=
  kernelMaskOfSupport3_pos (assignment.support_nonempty i)

theorem IndexFourFiberAssignment.kernelMask_lt_eight {xs : List Nat}
    (assignment : IndexFourFiberAssignment xs) (i : IndexFourFiberRow xs) :
    assignment.kernelMask i < 8 :=
  kernelMaskOfSupport3_lt_eight (assignment.support i)

@[simp] theorem IndexFourFiberAssignment.kernelMask_testBit {xs : List Nat}
    (assignment : IndexFourFiberAssignment xs) (i : IndexFourFiberRow xs)
    (b : Fin 3) :
    (assignment.kernelMask i).testBit b = decide (b ∈ assignment.support i) := by
  simp [IndexFourFiberAssignment.kernelMask]

@[simp] theorem IndexFourFiberAssignment.kernelMask_supportSize {xs : List Nat}
    (assignment : IndexFourFiberAssignment xs) (i : IndexFourFiberRow xs) :
    kernelSupportSize3 (assignment.kernelMask i) = (assignment.support i).card := by
  simp [IndexFourFiberAssignment.kernelMask]

theorem IndexFourFiberAssignment.kernelMask_indexRelation {xs : List Nat}
    (assignment : IndexFourFiberAssignment xs) (i : IndexFourFiberRow xs) :
    (i : Nat) * kernelSupportSize3 (assignment.kernelMask i) =
      4 * assignment.induced i := by
  simpa using assignment.index_relation i

theorem IndexFourFiberAssignment.kernelMask_sameBoxGcd {xs : List Nat}
    (assignment : IndexFourFiberAssignment xs) (b : Fin 3)
    (i j : IndexFourFiberRow xs) (hij : i ≠ j)
    (hi : (assignment.kernelMask i).testBit b = true)
    (hj : (assignment.kernelMask j).testBit b = true) :
    1 < Nat.gcd (assignment.induced i) (assignment.induced j) := by
  apply assignment.sameBoxGcd b i j hij
  · simpa using hi
  · simpa using hj

end ErdosProblems.E274
