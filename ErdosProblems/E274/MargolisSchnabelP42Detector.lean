import ErdosProblems.E274.MargolisSchnabelP42
import ErdosProblems.E274.ObstructionSelection
import ErdosProblems.E274.FiniteQuotientBridge

/-!
# Proposition 4.2 as an executable-detector corollary

This file closes the bridge from a `containsP42` witness in the sorted index
profile of an exact partition to the locally formalized finite-group theorem.
For an arbitrary ambient group, the partition is first transported to its
finite common-normal-core quotient, which preserves the complete index list.
-/

namespace ErdosProblems.E274

universe u

/-- A Proposition 4.2 detector witness cannot occur in an exact partition of
a finite group. -/
theorem p42DetectorCorollary_finite
    {G : Type u} [Group G] [Finite G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP42DetectorWitness
      (sortedIndexList H hinjective)) : False := by
  let xs := sortedIndexList H hinjective
  rcases hdetector with ⟨rs, hsub, hlen, hcop⟩
  have hrsNodup : rs.Nodup :=
    detectorResidual_nodup (sortedIndexList_nodup H hinjective) hsub
  let r : Fin 3 → ℕ := fixedLengthFamily rs hlen
  let a : Fin 3 → ℕ := fun i ↦ 2 * r i
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
  let e : Fin 3 ↪ Fin n :=
    selectedIndexEmbedding H hinjective a haMem haInjective
  have hindex (i : Fin 3) : (H (e i)).index = 2 * r i := by
    simp [e, a, xs]
  have hrCoprime : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j) :=
    fixedLengthFamily_pairwise (fun _ _ h ↦ h.symm) hlen hcop
  have hharmonic : IsHarmonicCosetFamily
      (fun i : Fin 3 ↦ g (e i)) (fun i : Fin 3 ↦ H (e i)) := by
    exact hpartition.selectedIndexFamily_harmonic
      hinjective a haMem haInjective
  have hgVector : (![g (e 0), g (e 1), g (e 2)] : Fin 3 → G) =
      (fun i : Fin 3 ↦ g (e i)) := by
    funext i
    fin_cases i <;> rfl
  have hHVector : (![H (e 0), H (e 1), H (e 2)] :
      Fin 3 → Subgroup G) = (fun i : Fin 3 ↦ H (e i)) := by
    funext i
    fin_cases i <;> rfl
  have hharmonicVector : IsHarmonicCosetFamily
      ![g (e 0), g (e 1), g (e 2)]
      ![H (e 0), H (e 1), H (e 2)] := by
    rw [hgVector, hHVector]
    exact hharmonic
  exact margolisSchnabelP42
    (H (e 0)) (H (e 1)) (H (e 2))
    (g (e 0)) (g (e 1)) (g (e 2))
    (r 0) (r 1) (r 2)
    (hindex 0) (hindex 1) (hindex 2)
    (hrCoprime 0 1 (by decide))
    (hrCoprime 0 2 (by decide))
    (hrCoprime 1 2 (by decide)) hharmonicVector

/-- The arbitrary-group Proposition 4.2 detector corollary, with the finite
quotient reduction and source proposition both proved locally in Lean. -/
theorem p42DetectorCorollary
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP42DetectorWitness
      (sortedIndexList H hinjective)) : False := by
  let Q := PartitionFiniteQuotient H
  let qg := quotientCellRepresentative g H
  let qH := quotientCellSubgroup H
  letI : Finite Q := partitionFiniteQuotient_finite hfinite
  have hqpartition : IsCosetPartition qg qH :=
    hpartition.toFiniteQuotient
  have hqinjective : Function.Injective (fun i ↦ (qH i).index) := by
    exact (quotientCellSubgroup_indices_injective_iff H).2 hinjective
  have hsorted : sortedIndexList qH hqinjective =
      sortedIndexList H hinjective :=
    quotientCellSubgroup_sortedIndexList H hqinjective hinjective
  apply p42DetectorCorollary_finite hqpartition hqinjective
  rw [hsorted]
  exact hdetector

end ErdosProblems.E274
