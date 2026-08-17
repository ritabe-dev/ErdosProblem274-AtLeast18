import ErdosProblems.E274.HarmonicObstructionSemantics
import ErdosProblems.E274.IndexProfile
import ErdosProblems.E274.CosetPartitionBasics

/-!
# Selecting obstruction subfamilies from a sorted index profile

The executable obstruction detectors return short lists of residual indices.
This file supplies the implementation-independent group-side selection step:
any duplicate-free list of actual subgroup indices occurring in a sorted
profile determines an embedding into the labelled cells of the partition.

The resulting subfamily inherits pairwise disjointness from the original
coset partition.  These lemmas are shared by the local formalizations of
Margolis--Schnabel Propositions 4.2, 4.3, 4.5, and 4.7.
-/

namespace ErdosProblems.E274

universe u

/-- Regard a list of known length as a family indexed by the corresponding
finite type. -/
def fixedLengthFamily {α : Type*} (xs : List α) {k : ℕ}
    (hlen : xs.length = k) : Fin k → α :=
  fun i ↦ xs.get (Fin.cast hlen.symm i)

theorem fixedLengthFamily_mem {α : Type*} (xs : List α) {k : ℕ}
    (hlen : xs.length = k) (i : Fin k) :
    fixedLengthFamily xs hlen i ∈ xs := by
  exact List.get_mem xs (Fin.cast hlen.symm i)

theorem fixedLengthFamily_injective {α : Type*} {xs : List α} {k : ℕ}
    (hlen : xs.length = k) (hnodup : xs.Nodup) :
    Function.Injective (fixedLengthFamily xs hlen) := by
  intro i j hij
  have hcast : Fin.cast hlen.symm i = Fin.cast hlen.symm j :=
    hnodup.injective_get hij
  exact (Fin.cast_injective hlen.symm) hcast

/-- A symmetric pairwise relation on a list transfers to its fixed-length
family for every pair of distinct coordinates. -/
theorem fixedLengthFamily_pairwise
    {α : Type*} {R : α → α → Prop} (hsymm : Symmetric R)
    {xs : List α} {k : ℕ} (hlen : xs.length = k)
    (hpair : xs.Pairwise R) :
    ∀ i j, i ≠ j → R (fixedLengthFamily xs hlen i)
      (fixedLengthFamily xs hlen j) := by
  intro i j hij
  let i' : Fin xs.length := Fin.cast hlen.symm i
  let j' : Fin xs.length := Fin.cast hlen.symm j
  have hne : i' ≠ j' := by
    intro heq
    exact hij ((Fin.cast_injective hlen.symm) heq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hpair.rel_get_of_lt hlt
  · exact hsymm (hpair.rel_get_of_lt hgt)

/-- The sorted index profile has no repeated entries. -/
theorem sortedIndexList_nodup
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index)) :
    (sortedIndexList H hinjective).Nodup :=
  (sortedIndexList_pairwise_lt H hinjective).nodup

/-- Dividing a duplicate-free list of multiples of a positive number by that
number preserves duplicate-freeness. -/
theorem divisiblePool_nodup {xs : List ℕ} (hxs : xs.Nodup) {m : ℕ}
    : ((xs.filter (fun x ↦ decide (x % m = 0))).map (· / m)).Nodup := by
  apply (hxs.filter _).map_on
  intro x hx y hy hdiv
  rw [List.mem_filter] at hx hy
  have hxmod : x % m = 0 := of_decide_eq_true hx.2
  have hymod : y % m = 0 := of_decide_eq_true hy.2
  calc
    x = x % m + m * (x / m) := (Nat.mod_add_div x m).symm
    _ = m * (x / m) := by simp [hxmod]
    _ = m * (y / m) := by rw [hdiv]
    _ = y % m + m * (y / m) := by simp [hymod]
    _ = y := Nat.mod_add_div y m

/-- A residual list returned by a detector is duplicate-free whenever it is a
sublist of the corresponding divided pool. -/
theorem detectorResidual_nodup {xs rs : List ℕ} (hxs : xs.Nodup)
    {m : ℕ}
    (hsub : rs.Sublist
      ((xs.filter (fun x ↦ decide (x % m = 0))).map (· / m))) :
    rs.Nodup :=
  hsub.nodup (divisiblePool_nodup hxs)

/-- Recover a labelled cell whose subgroup has a prescribed index occurring
in the sorted profile. -/
noncomputable def selectedIndexCell
    {G : Type u} [Group G] {n k : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (a : Fin k → ℕ)
    (hmem : ∀ j, a j ∈ sortedIndexList H hinjective)
    (j : Fin k) : Fin n :=
  Classical.choose ((mem_sortedIndexList_iff H hinjective (a j)).mp (hmem j))

@[simp] theorem selectedIndexCell_index
    {G : Type u} [Group G] {n k : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (a : Fin k → ℕ)
    (hmem : ∀ j, a j ∈ sortedIndexList H hinjective)
    (j : Fin k) :
    (H (selectedIndexCell H hinjective a hmem j)).index = a j :=
  Classical.choose_spec
    ((mem_sortedIndexList_iff H hinjective (a j)).mp (hmem j))

/-- Distinct requested index values select distinct labelled cells. -/
theorem selectedIndexCell_injective
    {G : Type u} [Group G] {n k : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (a : Fin k → ℕ)
    (hmem : ∀ j, a j ∈ sortedIndexList H hinjective)
    (hainjective : Function.Injective a) :
    Function.Injective (selectedIndexCell H hinjective a hmem) := by
  intro i j hij
  apply hainjective
  rw [← selectedIndexCell_index H hinjective a hmem i,
    ← selectedIndexCell_index H hinjective a hmem j, hij]

/-- The embedding of a finite requested index family into the labelled cells
of the original partition. -/
noncomputable def selectedIndexEmbedding
    {G : Type u} [Group G] {n k : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (a : Fin k → ℕ)
    (hmem : ∀ j, a j ∈ sortedIndexList H hinjective)
    (hainjective : Function.Injective a) : Fin k ↪ Fin n :=
  ⟨selectedIndexCell H hinjective a hmem,
    selectedIndexCell_injective H hinjective a hmem hainjective⟩

@[simp] theorem selectedIndexEmbedding_index
    {G : Type u} [Group G] {n k : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (a : Fin k → ℕ)
    (hmem : ∀ j, a j ∈ sortedIndexList H hinjective)
    (hainjective : Function.Injective a)
    (j : Fin k) :
    (H (selectedIndexEmbedding H hinjective a hmem hainjective j)).index =
      a j :=
  selectedIndexCell_index H hinjective a hmem j

/-- The selected cells form a harmonic family because they are an injective
subfamily of the original exact partition. -/
theorem IsCosetPartition.selectedIndexFamily_harmonic
    {G : Type u} [Group G] {n k : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (a : Fin k → ℕ)
    (hmem : ∀ j, a j ∈ sortedIndexList H hinjective)
    (hainjective : Function.Injective a) :
    IsHarmonicCosetFamily
      (fun j ↦ g (selectedIndexEmbedding H hinjective a hmem hainjective j))
      (fun j ↦ H (selectedIndexEmbedding H hinjective a hmem hainjective j)) :=
  hpartition.harmonicSubfamily
    (selectedIndexEmbedding H hinjective a hmem hainjective)

end ErdosProblems.E274
