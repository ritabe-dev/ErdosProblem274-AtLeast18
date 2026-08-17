import ErdosProblems.E274.IndexProfile
import ErdosProblems.E274.HarmonicObstructionSemantics

/-!
# Margolis--Schnabel statement interface for E274

This file records the six source-shaped statement surfaces used by the
bounded proof.  All six fields are discharged locally in
`LocalMargolisSchnabelFacts`; this structure is an internal theorem-mapping
interface, not an external assumption of the final theorem.  The statements
correspond to Lemma 2.3(b,c) and the detector-level corollaries of
Propositions 4.2, 4.3, 4.5, and 4.7 from:

L. Margolis and O. Schnabel, *The Herzog--Schonheim Conjecture for Small
Groups and Harmonic Subgroups*, arXiv:1803.03569.

The detector corollaries use `containsPXX_eq_true_iff_witness` and the fact
that a subfamily of a coset partition is harmonic.  Keeping the six statements
in one structure makes the literature-to-Lean theorem map auditable while the
public endpoint remains closed.
-/

namespace ErdosProblems.E274

universe u

/-- Exact six-item internal statement interface used by the bounded proof.
`localMargolisSchnabelFacts` proves every field inside Lean. -/
structure MargolisSchnabelFacts : Prop where
  lemma2_3b :
    ∀ {G : Type u} [Group G] {n : ℕ}
      {g : Fin n → G} {H : Fin n → Subgroup G},
      IsCosetPartition g H →
      (∀ i, (H i).index ≠ 0) →
      Function.Injective (fun i ↦ (H i).index) →
      ∑ i : Fin n, (((H i).index : ℚ)⁻¹) = 1
  lemma2_3c :
    ∀ {G : Type u} [Group G] {n : ℕ}
      {g : Fin n → G} {H : Fin n → Subgroup G},
      IsCosetPartition g H →
      (∀ i, (H i).index ≠ 0) →
      Function.Injective (fun i ↦ (H i).index) →
      ∀ i j, i ≠ j → 1 < Nat.gcd (H i).index (H j).index
  prop4_2_detectorCorollary :
    ∀ {G : Type u} [Group G] {n : ℕ}
      {g : Fin n → G} {H : Fin n → Subgroup G}
      (_hpartition : IsCosetPartition g H)
      (_hfinite : ∀ i, (H i).index ≠ 0)
      (hinjective : Function.Injective (fun i ↦ (H i).index)),
      HasP42DetectorWitness (sortedIndexList H hinjective) → False
  prop4_3_detectorCorollary :
    ∀ {G : Type u} [Group G] {n : ℕ}
      {g : Fin n → G} {H : Fin n → Subgroup G}
      (_hpartition : IsCosetPartition g H)
      (_hfinite : ∀ i, (H i).index ≠ 0)
      (hinjective : Function.Injective (fun i ↦ (H i).index)),
      HasP43DetectorWitness (sortedIndexList H hinjective) → False
  prop4_5_detectorCorollary :
    ∀ {G : Type u} [Group G] {n : ℕ}
      {g : Fin n → G} {H : Fin n → Subgroup G}
      (_hpartition : IsCosetPartition g H)
      (_hfinite : ∀ i, (H i).index ≠ 0)
      (hinjective : Function.Injective (fun i ↦ (H i).index)),
      HasP45DetectorWitness (sortedIndexList H hinjective) → False
  prop4_7_detectorCorollary :
    ∀ {G : Type u} [Group G] {n : ℕ}
      {g : Fin n → G} {H : Fin n → Subgroup G}
      (_hpartition : IsCosetPartition g H)
      (_hfinite : ∀ i, (H i).index ≠ 0)
      (hinjective : Function.Injective (fun i ↦ (H i).index)),
      HasP47DetectorWitness (sortedIndexList H hinjective) → False

/-- The four detector statements imply that the sorted index profile passes
the combined executable obstruction guard. -/
theorem sortedIndexList_noPublishedObstruction
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hsource : MargolisSchnabelFacts.{u}) :
    containsPublishedObstruction (sortedIndexList H hinjective) = false := by
  let xs := sortedIndexList H hinjective
  have h42 : containsP42 xs = false := by
    cases h : containsP42 xs with
    | false => rfl
    | true =>
        exact False.elim <| hsource.prop4_2_detectorCorollary
          hpartition hfinite hinjective
            ((containsP42_eq_true_iff_witness xs).mp h)
  have h43 : containsP43 xs = false := by
    cases h : containsP43 xs with
    | false => rfl
    | true =>
        exact False.elim <| hsource.prop4_3_detectorCorollary
          hpartition hfinite hinjective
            ((containsP43_eq_true_iff_witness xs).mp h)
  have h45 : containsP45 xs = false := by
    cases h : containsP45 xs with
    | false => rfl
    | true =>
        exact False.elim <| hsource.prop4_5_detectorCorollary
          hpartition hfinite hinjective
            ((containsP45_eq_true_iff_witness xs).mp h)
  have h47 : containsP47 xs = false := by
    cases h : containsP47 xs with
    | false => rfl
    | true =>
        exact False.elim <| hsource.prop4_7_detectorCorollary
          hpartition hfinite hinjective
            ((containsP47_eq_true_iff_witness xs).mp h)
  simp [containsPublishedObstruction, xs, h42, h43, h45, h47]

end ErdosProblems.E274
