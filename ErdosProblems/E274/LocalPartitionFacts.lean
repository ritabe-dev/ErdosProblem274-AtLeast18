import ErdosProblems.E274.GroupFiberBasics

/-!
# Exact local consequences of a finite coset partition

This file proves, without imported mathematical assumptions, the two
elementary consequences recorded as Margolis--Schnabel Lemma 2.3(b),(c) in
the E274 proof interface:

* the reciprocal subgroup indices of an exact finite coset partition sum to
  one;
* distinct cells whose subgroups have finite index have subgroup-index gcd
  greater than one.

For the reciprocal-sum identity we use the common finite-index subgroup
`D = ⨅ i, H i`.  Refining every `g i H i` cell into left `D`-cosets gives
an explicit equivalence between the sigma type of all refined cells and
`G ⧸ D`.  Taking cardinalities gives the required identity.
-/

namespace ErdosProblems.E274

universe u

/-- The common subgroup used to refine every cell of a finite coset
partition into cosets of one subgroup. -/
private def commonPartitionSubgroup {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) : Subgroup G :=
  ⨅ i, H i

private theorem commonPartitionSubgroup_le
    {G : Type u} [Group G] {n : ℕ} (H : Fin n → Subgroup G) (i : Fin n) :
    commonPartitionSubgroup H ≤ H i := by
  exact iInf_le H i

/-- Map a refined cell, indexed by an `H i`-coset of the common subgroup,
to the corresponding common-subgroup coset in the ambient group. -/
private def refinedPartitionMap
    {G : Type u} [Group G] {n : ℕ}
    (g : Fin n → G) (H : Fin n → Subgroup G) :
    (Σ i, H i ⧸ (commonPartitionSubgroup H).subgroupOf (H i)) →
      G ⧸ commonPartitionSubgroup H
  | ⟨i, q⟩ => shiftedCellBoxEmbedding
      (commonPartitionSubgroup H) (H i) (g i) q

private theorem refinedPartitionMap_injective
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) :
    Function.Injective (refinedPartitionMap g H) := by
  rintro ⟨i, qi⟩ ⟨j, qj⟩ hq
  induction qi using QuotientGroup.induction_on with
  | _ hi =>
      induction qj using QuotientGroup.induction_on with
      | _ hj =>
          have hquot :
              QuotientGroup.mk (g i * (hi : G) : G) =
                QuotientGroup.mk (g j * (hj : G) : G) := hq
          have hDmem :
              (g i * (hi : G))⁻¹ * (g j * (hj : G)) ∈
                commonPartitionSubgroup H := by
            rwa [QuotientGroup.eq] at hquot
          have hcellI : InLeftCoset (g i) (H i) (g j * (hj : G)) := by
            have hmem := (H i).mul_mem hi.property
              (commonPartitionSubgroup_le H i hDmem)
            simpa [InLeftCoset, mul_inv_rev, mul_assoc] using hmem
          have hcellJ : InLeftCoset (g j) (H j) (g j * (hj : G)) := by
            simp [InLeftCoset]
          have hij : i = j := by
            by_contra hij
            exact hpartition.isHarmonicCosetFamily hij (g j * (hj : G))
              ⟨hcellI, hcellJ⟩
          subst j
          have hinner :
              (QuotientGroup.mk hi :
                  H i ⧸ (commonPartitionSubgroup H).subgroupOf (H i)) =
                QuotientGroup.mk hj :=
            (shiftedCellBoxEmbedding
              (commonPartitionSubgroup H) (H i) (g i)).injective hq
          exact Sigma.ext rfl (heq_of_eq hinner)

private theorem refinedPartitionMap_surjective
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) :
    Function.Surjective (refinedPartitionMap g H) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
      rcases hpartition x with ⟨i, hi, _⟩
      let h : H i := ⟨(g i)⁻¹ * x, hi⟩
      refine ⟨⟨i, QuotientGroup.mk h⟩, ?_⟩
      simp [refinedPartitionMap, h]

/-- Refining each exact partition cell by the common subgroup produces each
common-subgroup coset exactly once. -/
private noncomputable def refinedPartitionEquiv
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) :
    (Σ i, H i ⧸ (commonPartitionSubgroup H).subgroupOf (H i)) ≃
      G ⧸ commonPartitionSubgroup H :=
  Equiv.ofBijective (refinedPartitionMap g H)
    ⟨refinedPartitionMap_injective hpartition,
      refinedPartitionMap_surjective hpartition⟩

/-- The reciprocal indices in an exact finite coset partition sum to one.
This is the unconditional local replacement for the `lemma2_3b` field of
`MargolisSchnabelFacts`. -/
theorem IsCosetPartition.sum_inv_index_eq_one
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0) :
    ∑ i : Fin n, (((H i).index : ℚ)⁻¹) = 1 := by
  classical
  let D : Subgroup G := commonPartitionSubgroup H
  have hDfinite : D.FiniteIndex := by
    dsimp [D, commonPartitionSubgroup]
    exact Subgroup.finiteIndex_iInf fun i =>
      Subgroup.finiteIndex_iff.mpr (hfinite i)
  letI : D.FiniteIndex := hDfinite
  letI : Fintype (G ⧸ D) := Fintype.ofFinite (G ⧸ D)
  letI (i : Fin n) :
      Fintype (H i ⧸ D.subgroupOf (H i)) :=
    Fintype.ofFinite (H i ⧸ D.subgroupOf (H i))
  have hDle (i : Fin n) : D ≤ H i := by
    exact commonPartitionSubgroup_le H i
  have hcardDom (i : Fin n) :
      Fintype.card (H i ⧸ D.subgroupOf (H i)) = D.relIndex (H i) := by
    rw [← Nat.card_eq_fintype_card,
      ← (D.subgroupOf (H i)).index_eq_card]
    rfl
  have hcardCod : Fintype.card (G ⧸ D) = D.index := by
    rw [← Nat.card_eq_fintype_card, ← D.index_eq_card]
  have hsumRel : ∑ i : Fin n, D.relIndex (H i) = D.index := by
    have hcard := Fintype.card_congr (refinedPartitionEquiv hpartition)
    rw [Fintype.card_sigma] at hcard
    change
      (∑ i : Fin n, Fintype.card (H i ⧸ D.subgroupOf (H i))) =
        Fintype.card (G ⧸ D) at hcard
    simpa only [hcardDom, hcardCod] using hcard
  have hDne : (D.index : ℚ) ≠ 0 := by
    exact_mod_cast hDfinite.index_ne_zero
  apply (mul_left_cancel₀ hDne)
  calc
    (D.index : ℚ) * ∑ i : Fin n, (((H i).index : ℚ)⁻¹) =
        ∑ i : Fin n, (D.index : ℚ) * (((H i).index : ℚ)⁻¹) := by
          rw [Finset.mul_sum]
    _ = ∑ i : Fin n, (D.relIndex (H i) : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hmul :
          (D.relIndex (H i) : ℚ) * ((H i).index : ℚ) = (D.index : ℚ) := by
        exact_mod_cast D.relIndex_mul_index (hDle i)
      rw [← hmul, mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (hfinite i)), mul_one]
    _ = (D.index : ℚ) := by exact_mod_cast hsumRel
    _ = (D.index : ℚ) * 1 := by rw [mul_one]

/-- Distinct cells in an exact finite-index coset partition have subgroup
indices with gcd greater than one.  This is the unconditional local
replacement for the `lemma2_3c` field of `MargolisSchnabelFacts`. -/
theorem IsCosetPartition.gcd_index_gt_one
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0) :
    ∀ i j, i ≠ j → 1 < Nat.gcd (H i).index (H j).index := by
  intro i j hij
  exact gcd_gt_one_of_disjoint_leftCosets
    (H i) (H j) (g i) (g j) (hfinite i)
      (hpartition.isHarmonicCosetFamily hij)

end ErdosProblems.E274
