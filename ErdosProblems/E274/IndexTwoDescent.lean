import ErdosProblems.E274.CosetPartitionBasics

/-!
# Descent through an index-two cell

If one cell in a finite coset partition has subgroup index two, deleting that
cell and translating the complementary coset back into the index-two subgroup
produces a coset partition with one fewer cell.  The new subgroup indices are
the old indices divided by two.

This is the local group-theoretic part of the minimal-counterexample reduction
for E274.  It does not import any theorem from Margolis--Schnabel.
-/

namespace ErdosProblems.E274

universe u

/-- Left translation of every representative preserves a coset partition. -/
theorem IsCosetPartition.leftTranslate
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) (t : G) :
    IsCosetPartition (fun i ↦ t * g i) H := by
  intro x
  rcases hpartition (t⁻¹ * x) with ⟨i, hi, hunique⟩
  refine ⟨i, ?_, ?_⟩
  · simpa [InLeftCoset, mul_assoc] using hi
  · intro j hj
    apply hunique j
    simpa [InLeftCoset, mul_assoc] using hj

/-- Removing an index-two cell and translating the complementary coset gives
a partition of the index-two subgroup.  Each old index is twice the
corresponding new index. -/
theorem IsCosetPartition.descendIndexTwo
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin (n + 1) → G} {H : Fin (n + 1) → Subgroup G}
    (hpartition : IsCosetPartition g H) (k : Fin (n + 1))
    (hkIndex : (H k).index = 2) :
    ∃ (g' : Fin n → H k) (H' : Fin n → Subgroup (H k)),
      IsCosetPartition g' H' ∧
        ∀ j, (H' j).index * 2 = (H (k.succAbove j)).index := by
  let K : Subgroup G := H k
  let gNorm : Fin (n + 1) → G := fun i ↦ (g k)⁻¹ * g i
  have hnormalized : IsCosetPartition gNorm H := by
    simpa [gNorm] using hpartition.leftTranslate (g k)⁻¹
  have hgNormK : gNorm k = 1 := by
    simp [gNorm]
  have hnotMem (i : Fin (n + 1)) (hik : i ≠ k) : gNorm i ∉ K := by
    intro hiK
    have hown : InLeftCoset (gNorm i) (H i) (gNorm i) := by
      simp [InLeftCoset]
    have hkcell : InLeftCoset (gNorm k) (H k) (gNorm i) := by
      simpa [K, hgNormK, InLeftCoset] using hiK
    exact hnormalized.isHarmonicCosetFamily hik (gNorm i) ⟨hown, hkcell⟩
  have hsubgroup (i : Fin (n + 1)) (hik : i ≠ k) : H i ≤ K := by
    intro y hy
    have hgi : gNorm i ∉ K := hnotMem i hik
    have hproduct : gNorm i * y ∉ K := by
      intro hproductK
      have hown : InLeftCoset (gNorm i) (H i) (gNorm i * y) := by
        simpa [InLeftCoset, mul_assoc] using hy
      have hkcell : InLeftCoset (gNorm k) (H k) (gNorm i * y) := by
        simpa [K, hgNormK, InLeftCoset] using hproductK
      exact hnormalized.isHarmonicCosetFamily hik (gNorm i * y)
        ⟨hown, hkcell⟩
    by_contra hyK
    have : gNorm i * y ∈ K :=
      (K.mul_mem_iff_of_index_two (by simpa [K] using hkIndex)).2
        (iff_of_false hgi hyK)
    exact hproduct this
  rcases (K.index_eq_two_iff_exists_notMem_and').mp
      (by simpa [K] using hkIndex) with ⟨a, haK, haCover⟩
  let oldIndex : Fin n → Fin (n + 1) := k.succAbove
  have holdIndexNe (j : Fin n) : oldIndex j ≠ k := by
    exact Fin.succAbove_ne k j
  have hrepMem (j : Fin n) : a * gNorm (oldIndex j) ∈ K := by
    exact (haCover (gNorm (oldIndex j))).resolve_right
      (hnotMem (oldIndex j) (holdIndexNe j))
  let g' : Fin n → K := fun j ↦ ⟨a * gNorm (oldIndex j), hrepMem j⟩
  let H' : Fin n → Subgroup K := fun j ↦
    (H (oldIndex j)).subgroupOf K
  have hpartition' : IsCosetPartition g' H' := by
    intro x
    let y : G := a⁻¹ * (x : G)
    have hainvK : a⁻¹ ∉ K := by
      simpa using haK
    have hyK : y ∉ K := by
      rw [show y = a⁻¹ * (x : G) by rfl,
        K.mul_mem_iff_of_index_two (by simpa [K] using hkIndex)]
      simp [hainvK, x.property]
    rcases hnormalized y with ⟨i, hi, hunique⟩
    have hik : i ≠ k := by
      intro hik
      subst i
      apply hyK
      simpa [hgNormK, InLeftCoset] using hi
    rcases Fin.exists_succAbove_eq hik with ⟨j, hj⟩
    have hjIndex : oldIndex j = i := by
      simpa [oldIndex] using hj
    refine ⟨j, ?_, ?_⟩
    · change (a * gNorm (oldIndex j))⁻¹ * (x : G) ∈ H (oldIndex j)
      simpa [InLeftCoset, y, hjIndex, mul_assoc] using hi
    · intro j' hj'
      change (a * gNorm (oldIndex j'))⁻¹ * (x : G) ∈
        H (oldIndex j') at hj'
      have hjOld :
          InLeftCoset (gNorm (oldIndex j')) (H (oldIndex j')) y := by
        simpa [InLeftCoset, y, mul_assoc] using hj'
      have holdEq : oldIndex j' = i := hunique (oldIndex j') hjOld
      apply Fin.succAbove_right_injective (p := k)
      simpa [oldIndex, hjIndex] using holdEq
  refine ⟨g', H', hpartition', ?_⟩
  intro j
  have hle : H (oldIndex j) ≤ K :=
    hsubgroup (oldIndex j) (holdIndexNe j)
  simpa [H', K, oldIndex, Subgroup.relIndex, hkIndex] using
    (Subgroup.relIndex_mul_index hle)

/-- In a one-cell coset partition, the unique subgroup is the whole group and
therefore has index one. -/
theorem IsCosetPartition.singletonIndexEqOne
    {G : Type u} [Group G]
    {g : Fin 1 → G} {H : Fin 1 → Subgroup G}
    (hpartition : IsCosetPartition g H) : (H 0).index = 1 := by
  apply Subgroup.index_eq_one.mpr
  apply top_unique
  intro x _hx
  rcases hpartition (g 0 * x) with ⟨i, hi, _hunique⟩
  have hiZero : i = 0 := Subsingleton.elim _ _
  subst i
  simpa [InLeftCoset, mul_assoc] using hi

/-- A two-cell distinct-index partition cannot contain an index-two cell. -/
theorem noIndexTwoInTwoCellDistinctPartition
    {G : Type u} [Group G]
    {g : Fin 2 → G} {H : Fin 2 → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin 2) (hk : (H k).index = 2) : False := by
  rcases hpartition.descendIndexTwo k hk with
    ⟨g', H', hpartition', hindices⟩
  have hnewIndex : (H' 0).index = 1 := hpartition'.singletonIndexEqOne
  have hotherIndex : (H (k.succAbove 0)).index = 2 := by
    rw [← hindices 0, hnewIndex, one_mul]
  have heq : k.succAbove 0 = k :=
    hinjective (hotherIndex.trans hk.symm)
  exact (Fin.succAbove_ne k 0) heq

/-- A concrete distinct-index partition with an index-two cell produces a
distinct-index counterexample with one fewer cell. -/
theorem HasDistinctIndexCosetPartition_of_descendIndexTwo
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin (n + 1) → G} {H : Fin (n + 1) → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin (n + 1)) (hk : (H k).index = 2) :
    HasDistinctIndexCosetPartition.{u} n := by
  rcases hpartition.descendIndexTwo k hk with ⟨g', H', hpartition', hindices⟩
  refine ⟨H k, inferInstance, g', H', hpartition', ?_, ?_⟩
  · intro j hj
    apply hfinite (k.succAbove j)
    rw [← hindices j, hj, zero_mul]
  · intro i j hij
    apply Fin.succAbove_right_injective (p := k)
    apply hinjective
    change (H' i).index = (H' j).index at hij
    change (H (k.succAbove i)).index = (H (k.succAbove j)).index
    rw [← hindices i, ← hindices j, hij]

end ErdosProblems.E274
