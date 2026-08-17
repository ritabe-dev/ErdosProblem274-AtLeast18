import ErdosProblems.E274.FiberMaskBasics
import Mathlib.Data.List.NodupEquivFin

/-!
# Direct declarative-to-mask bridge for E274

This module converts an `IndexFourFiberAssignment (4 :: rows)` directly into
an ordered list of three-bit support masks.  It does not pass through the
breadth-first executable search.  The ordered mask witness retains exactly the
three facts consumed by the finite BitVec certificate:

* `n * popcount(mask) = 4 * induced`;
* exact reciprocal capacity in each of the three labelled columns;
* pairwise gcd greater than one for rows sharing a column.
-/

namespace ErdosProblems.E274

/-- For a duplicate-free tail not containing four, list position is equivalent
to the non-anchor row subtype of `4 :: rows`. -/
def tailRowEquiv4 (rows : List Nat) (hnodup : rows.Nodup) (hfour : 4 ∉ rows) :
    Fin rows.length ≃ IndexFourFiberRow (4 :: rows) :=
  (hnodup.getEquiv rows).trans <|
    (Equiv.refl Nat).subtypeEquiv fun x => by
      simp only [List.mem_cons, List.mem_toFinset, Finset.mem_erase]
      constructor
      · intro hx
        exact ⟨fun h => hfour (h ▸ hx), Or.inr hx⟩
      · rintro ⟨_, h | hx⟩
        · exact (by contradiction)
        · exact hx

@[simp] theorem tailRowEquiv4_coe (rows : List Nat) (hnodup : rows.Nodup)
    (hfour : 4 ∉ rows) (i : Fin rows.length) :
    ((tailRowEquiv4 rows hnodup hfour i : IndexFourFiberRow (4 :: rows)) : Nat) =
      rows.get i := rfl

/-- Ordered support-mask data, retaining the rational capacity identity exactly
as it appears in the declarative group bridge. -/
structure OrderedFiberMaskAssignment4 (rows : List Nat) where
  mask : Fin rows.length → Nat
  induced : Fin rows.length → Nat
  mask_pos : ∀ i, 1 ≤ mask i
  mask_lt_eight : ∀ i, mask i < 8
  induced_ne_zero : ∀ i, induced i ≠ 0
  index_relation :
    ∀ i, rows.get i * kernelSupportSize3 (mask i) = 4 * induced i
  capacity :
    ∀ b : Fin 3,
      ∑ i : {i : Fin rows.length // (mask i).testBit b = true},
        (((induced i.1 : Nat) : ℚ)⁻¹) = 1
  sameBoxGcd :
    ∀ b : Fin 3, ∀ i j : Fin rows.length,
      i ≠ j → (mask i).testBit b = true → (mask j).testBit b = true →
        1 < Nat.gcd (induced i) (induced j)

/-- The fixed-width mask consumed by the split finite certificates. -/
def OrderedFiberMaskAssignment4.bitMask {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (i : Fin rows.length) :
    BitVec 3 :=
  BitVec.ofNat 3 (assignment.mask i)

@[simp] theorem OrderedFiberMaskAssignment4.bitMask_toNat {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (i : Fin rows.length) :
    (assignment.bitMask i).toNat = assignment.mask i := by
  rw [OrderedFiberMaskAssignment4.bitMask, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (assignment.mask_lt_eight i)

/-- Rational reciprocal capacity can be scaled to exact natural-number
capacity whenever every induced index divides the chosen scale. -/
theorem sum_scale_div_eq_of_mask_reciprocal_sum
    {ι : Type*} [Fintype ι] (e : ι → Nat) (scale : Nat)
    (hne : ∀ i, e i ≠ 0) (hdvd : ∀ i, e i ∣ scale)
    (hcapacity : ∑ i, (((e i : Nat) : ℚ)⁻¹) = 1) :
    ∑ i, scale / e i = scale := by
  have hterm (i : ι) :
      (((scale / e i : Nat) : ℚ)) =
        (scale : ℚ) * ((e i : ℚ)⁻¹) := by
    rw [Nat.cast_div (hdvd i) (by exact_mod_cast hne i)]
    simp [div_eq_mul_inv]
  have hq : ((∑ i, scale / e i : Nat) : ℚ) = scale := by
    rw [Nat.cast_sum]
    simp_rw [hterm]
    rw [← Finset.mul_sum, hcapacity, mul_one]
  exact_mod_cast hq

theorem OrderedFiberMaskAssignment4.scaledCapacity {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale) (b : Fin 3) :
    ∑ i : {i : Fin rows.length // (assignment.mask i).testBit b = true},
        scale / assignment.induced i.1 = scale := by
  apply sum_scale_div_eq_of_mask_reciprocal_sum
  · exact fun i => assignment.induced_ne_zero i.1
  · exact fun i => hdvd i.1
  · exact assignment.capacity b

/-- Induced index computed directly from an ambient index and a three-bit
mask. -/
def semanticInducedIndex4 (index : Nat) (mask : BitVec 3) : Nat :=
  index * kernelSupportSize3 mask.toNat / 4

/-- A compact, profile-independent semantic specification for the finite
BitVec certificate. -/
def FiberMaskSemanticConstraint4 {k : Nat} (scale : Nat)
    (index : Fin k → Nat) (mask : Fin k → BitVec 3) : Prop :=
  (∀ i, 1 ≤ (mask i).toNat) ∧
  (∀ i, (mask i).toNat < 8) ∧
  (∀ i, index i * kernelSupportSize3 (mask i).toNat % 4 = 0) ∧
  (∀ b : Fin 3,
    (∑ i : Fin k,
      if (mask i).toNat.testBit b then
        scale / semanticInducedIndex4 (index i) (mask i)
      else 0) = scale) ∧
  (∀ b : Fin 3, ∀ i j : Fin k,
    i ≠ j → (mask i).toNat.testBit b = true →
      (mask j).toNat.testBit b = true →
      1 < Nat.gcd
        (semanticInducedIndex4 (index i) (mask i))
        (semanticInducedIndex4 (index j) (mask j)))

theorem OrderedFiberMaskAssignment4.semanticInduced_bitMask {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (i : Fin rows.length) :
    semanticInducedIndex4 (rows.get i) (assignment.bitMask i) =
      assignment.induced i := by
  rw [semanticInducedIndex4, assignment.bitMask_toNat]
  have hrelation := assignment.index_relation i
  omega

/-- The direct ordered witness satisfies the generic BitVec semantics whenever
the chosen profile scale is divisible by each induced index. -/
theorem OrderedFiberMaskAssignment4.toSemanticConstraint4 {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale) :
    FiberMaskSemanticConstraint4 scale rows.get assignment.bitMask := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [assignment.bitMask_toNat]
    exact assignment.mask_pos i
  · intro i
    rw [assignment.bitMask_toNat]
    exact assignment.mask_lt_eight i
  · intro i
    rw [assignment.bitMask_toNat]
    have hrelation := assignment.index_relation i
    omega
  · intro b
    have hscaled := assignment.scaledCapacity scale hdvd b
    simp_rw [assignment.bitMask_toNat, assignment.semanticInduced_bitMask]
    calc
      (∑ i : Fin rows.length,
          if (assignment.mask i).testBit b then
            scale / assignment.induced i else 0) =
          (Finset.univ.filter
              (fun i : Fin rows.length => (assignment.mask i).testBit b = true)).sum
            (fun i => scale / assignment.induced i) := by
              rw [Finset.sum_ite]
              simp
      _ = ∑ i : {i : Fin rows.length //
          (assignment.mask i).testBit b = true},
          scale / assignment.induced i.1 := by
            apply Finset.sum_subtype
            simp
      _ = scale := hscaled
  · intro b i j hij hi hj
    rw [assignment.semanticInduced_bitMask, assignment.semanticInduced_bitMask]
    apply assignment.sameBoxGcd b i j hij
    · simpa only [assignment.bitMask_toNat] using hi
    · simpa only [assignment.bitMask_toNat] using hj

/-- Restrict the row equivalence to the rows whose masks select one fixed
column. -/
def selectedTailRowEquiv4 {rows : List Nat} (hnodup : rows.Nodup)
    (hfour : 4 ∉ rows) (assignment : IndexFourFiberAssignment (4 :: rows))
    (b : Fin 3) :
    {i : Fin rows.length //
      (assignment.kernelMask (tailRowEquiv4 rows hnodup hfour i)).testBit b = true} ≃
    {j : IndexFourFiberRow (4 :: rows) // b ∈ assignment.support j} :=
  (tailRowEquiv4 rows hnodup hfour).subtypeEquiv fun i => by
    simp

/-- A declarative index-four assignment gives the ordered mask witness used by
the finite certificate. -/
def IndexFourFiberAssignment.toOrderedMaskAssignment4 {rows : List Nat}
    (assignment : IndexFourFiberAssignment (4 :: rows))
    (hnodup : rows.Nodup) (hfour : 4 ∉ rows) :
    OrderedFiberMaskAssignment4 rows where
  mask i := assignment.kernelMask (tailRowEquiv4 rows hnodup hfour i)
  induced i := assignment.induced (tailRowEquiv4 rows hnodup hfour i)
  mask_pos i := assignment.kernelMask_pos _
  mask_lt_eight i := assignment.kernelMask_lt_eight _
  induced_ne_zero i := assignment.induced_ne_zero _
  index_relation i := by
    simpa using assignment.kernelMask_indexRelation
      (tailRowEquiv4 rows hnodup hfour i)
  capacity b := by
    let e := selectedTailRowEquiv4 hnodup hfour assignment b
    calc
      (∑ i : {i : Fin rows.length //
          (assignment.kernelMask (tailRowEquiv4 rows hnodup hfour i)).testBit b = true},
          (((assignment.induced (tailRowEquiv4 rows hnodup hfour i.1) : Nat) : ℚ)⁻¹)) =
          ∑ j : {j : IndexFourFiberRow (4 :: rows) // b ∈ assignment.support j},
            (((assignment.induced j.1 : Nat) : ℚ)⁻¹) := by
              simpa [e, selectedTailRowEquiv4] using
                (e.sum_comp (fun j : {j : IndexFourFiberRow (4 :: rows) //
                  b ∈ assignment.support j} =>
                    (((assignment.induced j.1 : Nat) : ℚ)⁻¹)))
      _ = 1 := assignment.capacity b
  sameBoxGcd b i j hij hi hj := by
    apply assignment.kernelMask_sameBoxGcd b
      (tailRowEquiv4 rows hnodup hfour i)
      (tailRowEquiv4 rows hnodup hfour j)
    · exact fun heq => hij ((tailRowEquiv4 rows hnodup hfour).injective heq)
    · exact hi
    · exact hj

end ErdosProblems.E274
