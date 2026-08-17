import ErdosProblems.E274.MargolisSchnabelP43
import ErdosProblems.E274.ObstructionSelection
import ErdosProblems.E274.FiniteQuotientBridge

/-!
# Proposition 4.3 as an executable-detector corollary

This file selects the four cells exposed by `containsP43` and applies the
locally proved finite-group obstruction.  The arbitrary-group statement then
uses the common-normal-core finite quotient, which preserves the complete
index profile.
-/

namespace ErdosProblems.E274

universe u

/-- A Proposition 4.3 detector witness cannot occur in an exact partition of
a finite group. -/
theorem p43DetectorCorollary_finite
    {G : Type u} [Group G] [Finite G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP43DetectorWitness
      (sortedIndexList H hinjective)) : False := by
  let xs := sortedIndexList H hinjective
  rcases hdetector with ⟨rs, hsub, hlen, hcop⟩
  have hrsNodup : rs.Nodup :=
    detectorResidual_nodup (sortedIndexList_nodup H hinjective) hsub
  let r : Fin 4 → ℕ := fixedLengthFamily rs hlen
  let a : Fin 4 → ℕ := fun i ↦ 3 * r i
  have hrInjective : Function.Injective r :=
    fixedLengthFamily_injective hlen hrsNodup
  have haInjective : Function.Injective a := by
    intro i j hij
    apply hrInjective
    dsimp [a] at hij
    omega
  have haMem : ∀ i, a i ∈ xs := by
    intro i
    apply scaled_mem_of_mem_divisiblePool
    apply hsub.subset
    exact fixedLengthFamily_mem rs hlen i
  let e : Fin 4 ↪ Fin n :=
    selectedIndexEmbedding H hinjective a haMem haInjective
  have hindex (i : Fin 4) : (H (e i)).index = 3 * r i := by
    simp [e, a, xs]
  have hrCoprime : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j) :=
    fixedLengthFamily_pairwise (fun _ _ h ↦ h.symm) hlen hcop
  have hharmonic : IsHarmonicCosetFamily
      (fun i : Fin 4 ↦ g (e i)) (fun i : Fin 4 ↦ H (e i)) :=
    hpartition.selectedIndexFamily_harmonic
      hinjective a haMem haInjective
  exact margolisSchnabel_prop4_3_finite
    (fun i : Fin 4 ↦ g (e i)) (fun i : Fin 4 ↦ H (e i)) r
    hindex hrCoprime hharmonic

/-- The arbitrary-group Proposition 4.3 detector corollary. -/
theorem p43DetectorCorollary
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP43DetectorWitness
      (sortedIndexList H hinjective)) : False := by
  let Q := PartitionFiniteQuotient H
  let qg := quotientCellRepresentative g H
  let qH := quotientCellSubgroup H
  letI : Finite Q := partitionFiniteQuotient_finite hfinite
  have hqpartition : IsCosetPartition qg qH :=
    hpartition.toFiniteQuotient
  have hqinjective : Function.Injective (fun i ↦ (qH i).index) :=
    (quotientCellSubgroup_indices_injective_iff H).2 hinjective
  have hsorted : sortedIndexList qH hqinjective =
      sortedIndexList H hinjective :=
    quotientCellSubgroup_sortedIndexList H hqinjective hinjective
  apply p43DetectorCorollary_finite hqpartition hqinjective
  rw [hsorted]
  exact hdetector

end ErdosProblems.E274
