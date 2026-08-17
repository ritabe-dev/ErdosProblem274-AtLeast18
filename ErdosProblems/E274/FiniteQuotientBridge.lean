import ErdosProblems.E274.IndexProfile

/-!
# The finite normal-core quotient for E274

This file formalizes the standard reduction of a finite-index coset partition
of an arbitrary group to a partition of a finite quotient.  For a family
`H : Fin n → Subgroup G`, the common kernel is the intersection of the normal
cores of the `H i`.  It is normal, has finite index when every `H i` does, and
is contained in every `H i`.

Consequently, mapping the representatives and subgroups to the common-core
quotient preserves the complete cells (by an exact preimage identity), the
partition, and every subgroup index.  No finiteness assumption on `G` is used.
-/

namespace ErdosProblems.E274

universe u

/-- The common normal subgroup used to make every cell descend to one finite
quotient. -/
def partitionNormalCore {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) : Subgroup G :=
  ⨅ i, (H i).normalCore

instance partitionNormalCore_normal {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) : (partitionNormalCore H).Normal := by
  apply Subgroup.normal_iInf_normal
  intro i
  infer_instance

/-- The common normal core lies in every subgroup in the family. -/
theorem partitionNormalCore_le {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (i : Fin n) :
    partitionNormalCore H ≤ H i :=
  (iInf_le (fun j ↦ (H j).normalCore) i).trans (H i).normalCore_le

/-- A finite intersection of normal cores of finite-index subgroups still has
finite index. -/
theorem partitionNormalCore_index_ne_zero
    {G : Type u} [Group G] {n : ℕ} {H : Fin n → Subgroup G}
    (hfinite : ∀ i, (H i).index ≠ 0) :
    (partitionNormalCore H).index ≠ 0 := by
  apply Subgroup.index_iInf_ne_zero
  intro i
  letI : (H i).FiniteIndex := ⟨hfinite i⟩
  exact Subgroup.FiniteIndex.index_ne_zero

/-- The quotient by the common normal core. -/
abbrev PartitionFiniteQuotient {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) :=
  G ⧸ partitionNormalCore H

/-- The quotient group is finite when every subgroup in the family has finite
index. -/
theorem partitionFiniteQuotient_finite
    {G : Type u} [Group G] {n : ℕ} {H : Fin n → Subgroup G}
    (hfinite : ∀ i, (H i).index ≠ 0) :
    Finite (PartitionFiniteQuotient H) := by
  letI : (partitionNormalCore H).FiniteIndex :=
    ⟨partitionNormalCore_index_ne_zero hfinite⟩
  infer_instance

/-- The representative of a descended cell. -/
def quotientCellRepresentative
    {G : Type u} [Group G] {n : ℕ}
    (g : Fin n → G) (H : Fin n → Subgroup G) :
    Fin n → PartitionFiniteQuotient H :=
  fun i ↦ QuotientGroup.mk' (partitionNormalCore H) (g i)

/-- The subgroup of a descended cell. -/
def quotientCellSubgroup
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) :
    Fin n → Subgroup (PartitionFiniteQuotient H) :=
  fun i ↦ (H i).map (QuotientGroup.mk' (partitionNormalCore H))

/-- General exact membership identity for a quotient by a normal subgroup
contained in the cell subgroup. -/
theorem inLeftCoset_map_quotient_iff
    {G : Type u} [Group G] (N H : Subgroup G) [N.Normal]
    (hNH : N ≤ H) (a x : G) :
    InLeftCoset (QuotientGroup.mk' N a)
        (H.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N x) ↔
      InLeftCoset a H x := by
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hker : π.ker ≤ H := by
    simpa [π] using hNH
  have hcomap : (H.map π).comap π = H :=
    Subgroup.comap_map_eq_self hker
  change π (a⁻¹ * x) ∈ H.map π ↔ a⁻¹ * x ∈ H
  change a⁻¹ * x ∈ (H.map π).comap π ↔ a⁻¹ * x ∈ H
  rw [hcomap]

/-- Membership in a descended cell is equivalent to membership in the
original cell for every chosen lift. -/
@[simp] theorem inLeftCoset_quotientCell_iff
    {G : Type u} [Group G] {n : ℕ}
    (g : Fin n → G) (H : Fin n → Subgroup G)
    (i : Fin n) (x : G) :
    InLeftCoset (quotientCellRepresentative g H i)
        (quotientCellSubgroup H i)
        (QuotientGroup.mk' (partitionNormalCore H) x) ↔
      InLeftCoset (g i) (H i) x := by
  exact inLeftCoset_map_quotient_iff
    (partitionNormalCore H) (H i) (partitionNormalCore_le H i) (g i) x

/-- The full inverse image of a descended cell is exactly its original cell.
This simultaneously records preservation of coverage and disjointness. -/
theorem quotientCell_preimage
    {G : Type u} [Group G] {n : ℕ}
    (g : Fin n → G) (H : Fin n → Subgroup G) (i : Fin n) :
    (QuotientGroup.mk' (partitionNormalCore H)) ⁻¹'
        {q | InLeftCoset (quotientCellRepresentative g H i)
          (quotientCellSubgroup H i) q} =
      {x | InLeftCoset (g i) (H i) x} := by
  ext x
  exact inLeftCoset_quotientCell_iff g H i x

/-- A coset partition descends to the common normal-core quotient without
changing its labelled cells. -/
theorem IsCosetPartition.toFiniteQuotient
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) :
    IsCosetPartition (quotientCellRepresentative g H)
      (quotientCellSubgroup H) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (partitionNormalCore H) q
  obtain ⟨i, hi, hunique⟩ := hpartition x
  refine ⟨i, (inLeftCoset_quotientCell_iff g H i x).2 hi, ?_⟩
  intro j hj
  exact hunique j ((inLeftCoset_quotientCell_iff g H j x).1 hj)

/-- Pairwise disjointness of all labelled cells is equivalent before and after
the common-core quotient.  The reverse implication uses surjectivity of the
quotient map; the forward implication uses the exact membership identity. -/
theorem quotientCells_harmonic_iff
    {G : Type u} [Group G] {n : ℕ}
    (g : Fin n → G) (H : Fin n → Subgroup G) :
    IsHarmonicCosetFamily (quotientCellRepresentative g H)
        (quotientCellSubgroup H) ↔
      IsHarmonicCosetFamily g H := by
  constructor
  · intro hquot i j hij x hx
    exact hquot hij (QuotientGroup.mk' (partitionNormalCore H) x)
      ⟨(inLeftCoset_quotientCell_iff g H i x).2 hx.1,
        (inLeftCoset_quotientCell_iff g H j x).2 hx.2⟩
  · intro horig i j hij q hq
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (partitionNormalCore H) q
    subst q
    exact horig hij x
      ⟨(inLeftCoset_quotientCell_iff g H i x).1 hq.1,
        (inLeftCoset_quotientCell_iff g H j x).1 hq.2⟩

/-- Passing to the common normal-core quotient preserves every subgroup
index. -/
theorem quotientCellSubgroup_index
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (i : Fin n) :
    (quotientCellSubgroup H i).index = (H i).index := by
  apply Subgroup.index_map_eq
  · exact QuotientGroup.mk'_surjective (partitionNormalCore H)
  · simpa using partitionNormalCore_le H i

/-- Relative intersection indices are also preserved.  This records that the
intersection multipliers used by finite-group harmonic arguments do not
change in the common-core quotient. -/
theorem quotientCellSubgroup_relIndex
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (i j : Fin n) :
    (quotientCellSubgroup H i).relIndex (quotientCellSubgroup H j) =
      (H i).relIndex (H j) := by
  change ((H i).map (QuotientGroup.mk' (partitionNormalCore H))).relIndex
      ((H j).map (QuotientGroup.mk' (partitionNormalCore H))) =
    (H i).relIndex (H j)
  rw [Subgroup.relIndex_map_map]
  have hi : (QuotientGroup.mk' (partitionNormalCore H)).ker ≤ H i := by
    simpa using partitionNormalCore_le H i
  have hj : (QuotientGroup.mk' (partitionNormalCore H)).ker ≤ H j := by
    simpa using partitionNormalCore_le H j
  rw [sup_of_le_left hi, sup_of_le_left hj]

/-- Finiteness of every cell index is preserved exactly. -/
theorem quotientCellSubgroup_index_ne_zero_iff
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (i : Fin n) :
    (quotientCellSubgroup H i).index ≠ 0 ↔ (H i).index ≠ 0 := by
  rw [quotientCellSubgroup_index]

/-- Pairwise distinctness of the complete index profile is preserved exactly. -/
theorem quotientCellSubgroup_indices_injective_iff
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) :
    Function.Injective (fun i ↦ (quotientCellSubgroup H i).index) ↔
      Function.Injective (fun i ↦ (H i).index) := by
  simp_rw [quotientCellSubgroup_index]

/-- Sorting the index profile after quotienting produces literally the same
list.  Hence every detector depending only on the sorted ambient indices is
transported without a separate argument. -/
theorem quotientCellSubgroup_sortedIndexList
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hquotient : Function.Injective
      (fun i ↦ (quotientCellSubgroup H i).index))
    (horiginal : Function.Injective (fun i ↦ (H i).index)) :
    sortedIndexList (quotientCellSubgroup H) hquotient =
      sortedIndexList H horiginal := by
  have hfinset :
      indexFinset (quotientCellSubgroup H) hquotient =
        indexFinset H horiginal := by
    apply Finset.ext
    intro x
    simp [indexFinset, indexEmbedding, quotientCellSubgroup_index]
  unfold sortedIndexList
  rw [hfinset]

/-- Every pairwise gcd relation between cell indices is unchanged. -/
theorem quotientCellSubgroup_gcd
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (i j : Fin n) :
    Nat.gcd (quotientCellSubgroup H i).index
        (quotientCellSubgroup H j).index =
      Nat.gcd (H i).index (H j).index := by
  rw [quotientCellSubgroup_index, quotientCellSubgroup_index]

/-- The reciprocal-index density of the whole labelled family is unchanged. -/
theorem quotientCellSubgroup_reciprocalSum
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) :
    ∑ i : Fin n, (((quotientCellSubgroup H i).index : ℚ)⁻¹) =
      ∑ i : Fin n, (((H i).index : ℚ)⁻¹) := by
  apply Finset.sum_congr rfl
  intro i _hi
  rw [quotientCellSubgroup_index]

/-- The complete finite-quotient reduction, packaged in the form used by the
source-facing obstruction layer. -/
theorem finiteQuotientReduction
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0) :
    Finite (PartitionFiniteQuotient H) ∧
      IsCosetPartition (quotientCellRepresentative g H)
        (quotientCellSubgroup H) ∧
      (∀ i, (quotientCellSubgroup H i).index = (H i).index) := by
  exact ⟨partitionFiniteQuotient_finite hfinite,
    hpartition.toFiniteQuotient, quotientCellSubgroup_index H⟩

/-- A version of the counterexample surface whose ambient group is finite.
It is useful for applying literature results stated under a finite-group
standing convention. -/
def HasFiniteDistinctIndexCosetPartition (n : ℕ) : Prop :=
  ∃ (G : Type u) (_group : Group G) (_finite : Finite G)
      (g : Fin n → G) (H : Fin n → Subgroup G),
    letI := _group
    IsCosetPartition g H ∧
      (∀ i, (H i).index ≠ 0) ∧
      Function.Injective (fun i ↦ (H i).index)

/-- Every arbitrary-group distinct-index partition has a finite-group model
with the same number of cells and the same complete index profile. -/
theorem HasDistinctIndexCosetPartition.toFiniteQuotient {n : ℕ} :
    HasDistinctIndexCosetPartition.{u} n →
      HasFiniteDistinctIndexCosetPartition.{u} n := by
  rintro ⟨G, groupG, g, H, hpartition, hfinite, hinjective⟩
  letI : Group G := groupG
  let Q := PartitionFiniteQuotient H
  let qg := quotientCellRepresentative g H
  let qH := quotientCellSubgroup H
  have hQfinite : Finite Q := partitionFiniteQuotient_finite hfinite
  refine ⟨Q, inferInstance, hQfinite, qg, qH, ?_, ?_, ?_⟩
  · exact hpartition.toFiniteQuotient
  · intro i
    change (quotientCellSubgroup H i).index ≠ 0
    exact (quotientCellSubgroup_index_ne_zero_iff H i).2 (hfinite i)
  · change Function.Injective (fun i ↦ (quotientCellSubgroup H i).index)
    exact (quotientCellSubgroup_indices_injective_iff H).2 hinjective

end ErdosProblems.E274
