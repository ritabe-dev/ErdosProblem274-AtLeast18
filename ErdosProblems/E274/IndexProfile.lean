import ErdosProblems.E274.MinimalCounterexample

/-!
# Sorted index profiles of distinct-index partitions

This file converts an injective family of subgroup indices into the strictly
increasing list consumed by the exact arithmetic search.  It also transports
the reciprocal-sum and pairwise-gcd facts from the original `Fin n` family to
that sorted list.
-/

namespace ErdosProblems.E274

universe u

/-- The injective map from cells to their subgroup indices. -/
noncomputable def indexEmbedding
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index)) :
    Fin n ↪ ℕ :=
  ⟨fun i ↦ (H i).index, hinjective⟩

/-- The finite set of subgroup indices. -/
noncomputable def indexFinset
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index)) :
    Finset ℕ :=
  Finset.univ.map (indexEmbedding H hinjective)

/-- The subgroup indices in strictly increasing order. -/
noncomputable def sortedIndexList
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index)) :
    List ℕ :=
  (indexFinset H hinjective).sort

@[simp] theorem sortedIndexList_length
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index)) :
    (sortedIndexList H hinjective).length = n := by
  simp [sortedIndexList, indexFinset]

theorem sortedIndexList_pairwise_lt
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index)) :
    (sortedIndexList H hinjective).Pairwise (fun x y ↦ x < y) := by
  exact (indexFinset H hinjective).sortedLT_sort.pairwise

@[simp] theorem mem_sortedIndexList_iff
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (x : ℕ) :
    x ∈ sortedIndexList H hinjective ↔ ∃ i, (H i).index = x := by
  simp [sortedIndexList, indexFinset, indexEmbedding]

/-- Finite-index, nontrivial cells with no index two all have index greater
than two. -/
theorem sortedIndexList_all_gt_two
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) (hn : 2 ≤ n)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hnotTwo : ∀ i, (H i).index ≠ 2) :
    ∀ x ∈ sortedIndexList H hinjective, 2 < x := by
  intro x hx
  rcases (mem_sortedIndexList_iff H hinjective x).mp hx with ⟨i, rfl⟩
  have hnotOne := hpartition.indexNeOne_of_two_le hn i
  have hnotZero := hfinite i
  have hnotTwo' := hnotTwo i
  omega

/-- Transport a reciprocal-sum identity from the indexed family to the sorted
index list. -/
theorem sortedIndexList_reciprocalSum
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdensity : ∑ i : Fin n, (((H i).index : ℚ)⁻¹) = 1) :
    ((sortedIndexList H hinjective).map
      (fun x : ℕ ↦ ((x : ℚ)⁻¹))).sum = 1 := by
  let f : ℕ → ℚ := fun x ↦ ((x : ℚ)⁻¹)
  have hperm :=
    (Finset.sort_perm_toList (indexFinset H hinjective) (fun x y : ℕ ↦ x ≤ y)).map f
  calc
    ((sortedIndexList H hinjective).map
        (fun x : ℕ ↦ ((x : ℚ)⁻¹))).sum =
        ((sortedIndexList H hinjective).map f).sum := by simp [f]
    _ =
        (((indexFinset H hinjective).toList).map f).sum := by
      exact hperm.sum_eq
    _ = ∑ x ∈ indexFinset H hinjective, f x := by simp
    _ = ∑ i : Fin n, f ((H i).index) := by
      simp [indexFinset, indexEmbedding]
    _ = 1 := by simpa [f] using hdensity

/-- Transport pairwise non-coprimality from cells to their sorted index list. -/
theorem sortedIndexList_pairwise_gcd
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hgcd : ∀ i j, i ≠ j → 1 < Nat.gcd (H i).index (H j).index) :
    (sortedIndexList H hinjective).Pairwise
      (fun x y ↦ 1 < Nat.gcd x y) := by
  apply List.Pairwise.imp_of_mem _ (sortedIndexList_pairwise_lt H hinjective)
  intro a b ha hb hab
  rcases (mem_sortedIndexList_iff H hinjective a).mp ha with ⟨i, hi⟩
  rcases (mem_sortedIndexList_iff H hinjective b).mp hb with ⟨j, hj⟩
  have hij : i ≠ j := by
    intro hij
    subst j
    rw [hi] at hj
    omega
  simpa [hi, hj] using hgcd i j hij

end ErdosProblems.E274
