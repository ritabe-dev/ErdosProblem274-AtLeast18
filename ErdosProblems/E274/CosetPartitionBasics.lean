import ErdosProblems.E274.Problem

/-!
# Basic harmonic-family consequences of a coset partition

These lemmas isolate the elementary fact used by all four published
obstructions: every subfamily of a coset partition has pairwise disjoint
cosets.  No finite quotient or source theorem is used here.
-/

namespace ErdosProblems.E274

universe u v w

/-- A family of chosen left cosets has pairwise empty intersections. -/
def IsHarmonicCosetFamily {G : Type u} [Group G] {ι : Type v}
    (g : ι → G) (H : ι → Subgroup G) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ x : G,
    ¬(InLeftCoset (g i) (H i) x ∧ InLeftCoset (g j) (H j) x)

/-- Distinct cells of a coset partition are disjoint. -/
theorem IsCosetPartition.isHarmonicCosetFamily
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) :
    IsHarmonicCosetFamily g H := by
  intro i j hij x hx
  rcases hpartition x with ⟨k, hk, hunique⟩
  have hi : i = k := hunique i hx.1
  have hj : j = k := hunique j hx.2
  exact hij (hi.trans hj.symm)

/-- Injectively selecting a subfamily preserves pairwise disjointness. -/
theorem IsHarmonicCosetFamily.comp
    {G : Type u} [Group G] {ι : Type v} {κ : Type w}
    {g : ι → G} {H : ι → Subgroup G}
    (hharmonic : IsHarmonicCosetFamily g H) (f : κ ↪ ι) :
    IsHarmonicCosetFamily (fun k ↦ g (f k)) (fun k ↦ H (f k)) := by
  intro i j hij x hx
  exact hharmonic (f.injective.ne hij) x hx

/-- Every injectively selected subfamily of a coset partition is harmonic. -/
theorem IsCosetPartition.harmonicSubfamily
    {G : Type u} [Group G] {n : ℕ} {κ : Type v}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) (f : κ ↪ Fin n) :
    IsHarmonicCosetFamily (fun k ↦ g (f k)) (fun k ↦ H (f k)) :=
  hpartition.isHarmonicCosetFamily.comp f

/-- In a partition with at least two cells, no cell can use the whole group,
so no subgroup index is one. -/
theorem IsCosetPartition.indexNeOne_of_two_le
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H) (hn : 2 ≤ n) (i : Fin n) :
    (H i).index ≠ 1 := by
  intro hi
  have htop : H i = ⊤ := Subgroup.index_eq_one.mp hi
  have hcard : 1 < Fintype.card (Fin n) := by
    simpa using hn
  rcases Fintype.exists_ne_of_one_lt_card hcard i with ⟨j, hji⟩
  have hown : InLeftCoset (g j) (H j) (g j) := by
    simp [InLeftCoset]
  have hicell : InLeftCoset (g i) (H i) (g j) := by
    simp [InLeftCoset, htop]
  exact hpartition.isHarmonicCosetFamily hji (g j) ⟨hown, hicell⟩

end ErdosProblems.E274
