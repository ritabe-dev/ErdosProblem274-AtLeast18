import ErdosProblems.E274.MargolisSchnabelP47
import ErdosProblems.E274.ObstructionSelection
import ErdosProblems.E274.FiniteQuotientBridge

/-!
# Proposition 4.7 as an executable-detector corollary

This file selects the distinguished index-three cell, the second odd
index-three cell, and the three index-six cells exposed by `containsP47`.
It then applies the locally proved finite-group obstruction.  The
arbitrary-group statement uses the common-normal-core finite quotient, which
preserves the complete index profile.
-/

namespace ErdosProblems.E274

universe u

/-- A Proposition 4.7 detector witness cannot occur in an exact partition of
a finite group. -/
theorem p47DetectorCorollary_finite
    {G : Type u} [Group G] [Finite G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP47DetectorWitness
      (sortedIndexList H hinjective)) : False := by
  let xs := sortedIndexList H hinjective
  rcases hdetector with ⟨hthree, r₂, hr₂, rs, hsub, hlen, hcop⟩
  have hr₂Source := threeOddPool_mem_source hr₂
  have hrsNodup : rs.Nodup :=
    detectorResidual_nodup (sortedIndexList_nodup H hinjective) hsub
  let q : Fin 3 → ℕ := fixedLengthFamily rs hlen
  let t : Fin 4 → ℕ := ![r₂, q 0, q 1, q 2]
  let a : Fin 5 → ℕ := ![3, 3 * r₂, 6 * q 0, 6 * q 1, 6 * q 2]
  have hqInjective : Function.Injective q :=
    fixedLengthFamily_injective hlen hrsNodup
  have hq01 : q 0 ≠ q 1 := by
    intro h
    have : (0 : Fin 3) = 1 := hqInjective h
    omega
  have hq02 : q 0 ≠ q 2 := by
    intro h
    have : (0 : Fin 3) = 2 := hqInjective h
    omega
  have hq12 : q 1 ≠ q 2 := by
    intro h
    have : (1 : Fin 3) = 2 := hqInjective h
    omega
  have hthreeNeSecond : 3 ≠ 3 * r₂ := by
    intro h
    exact hr₂Source.2.2 (by omega)
  have hsecondNeThree : 3 * r₂ ≠ 3 := hthreeNeSecond.symm
  have hthreeNeHigh (s : ℕ) : 3 ≠ 6 * s := by omega
  have hhighNeThree (s : ℕ) : 6 * s ≠ 3 := (hthreeNeHigh s).symm
  have hsecondNeHigh (s : ℕ) : 3 * r₂ ≠ 6 * s := by
    intro h
    have hodd : r₂ % 2 = 1 := hr₂Source.2.1
    omega
  have hhighNeSecond (s : ℕ) : 6 * s ≠ 3 * r₂ :=
    (hsecondNeHigh s).symm
  have haInjective : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  have haMem : ∀ i, a i ∈ xs := by
    intro i
    fin_cases i
    · simpa [a, xs] using hthree
    · simpa [a, xs] using hr₂Source.1
    · simp only [a, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact scaled_mem_of_mem_divisiblePool
        (hsub.subset (fixedLengthFamily_mem rs hlen 0))
    · simp only [a, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact scaled_mem_of_mem_divisiblePool
        (hsub.subset (fixedLengthFamily_mem rs hlen 1))
    · simp only [a, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact scaled_mem_of_mem_divisiblePool
        (hsub.subset (fixedLengthFamily_mem rs hlen 2))
  let e : Fin 5 ↪ Fin n :=
    selectedIndexEmbedding H hinjective a haMem haInjective
  have hindex0 : (H (e 0)).index = 3 := by
    simp [e, a, xs]
  have hindex1 : (H (e 1)).index = 3 * r₂ := by
    simp [e, a, xs]
  have hindex2 : (H (e 2)).index = 6 * q 0 := by
    simp [e, a, xs]
  have hindex3 : (H (e 3)).index = 6 * q 1 := by
    simp [e, a, xs]
  have hindex4 : (H (e 4)).index = 6 * q 2 := by
    simp [e, a, xs]
  have hlen4 : (r₂ :: rs).length = 4 := by simp [hlen]
  have htCoprime : ∀ i j, i ≠ j → Nat.Coprime (t i) (t j) := by
    have hp := fixedLengthFamily_pairwise
      (fun _ _ h ↦ h.symm) hlen4 hcop
    intro i j hij
    have hpij := hp i j hij
    fin_cases i <;> fin_cases j <;>
      simpa [t, q, fixedLengthFamily, hlen4] using hpij
  have hharmonic : IsHarmonicCosetFamily
      (fun i : Fin 5 ↦ g (e i)) (fun i : Fin 5 ↦ H (e i)) :=
    hpartition.selectedIndexFamily_harmonic
      hinjective a haMem haInjective
  exact margolisSchnabel_prop4_7_finite
    (fun i : Fin 5 ↦ g (e i)) (fun i : Fin 5 ↦ H (e i))
    r₂ (q 0) (q 1) (q 2)
    hindex0 hindex1 hindex2 hindex3 hindex4
    (Nat.odd_iff.mpr hr₂Source.2.1)
    (by simpa [t] using htCoprime 0 1 (by decide))
    (by simpa [t] using htCoprime 0 2 (by decide))
    (by simpa [t] using htCoprime 0 3 (by decide))
    (by simpa [t] using htCoprime 1 2 (by decide))
    (by simpa [t] using htCoprime 1 3 (by decide))
    (by simpa [t] using htCoprime 2 3 (by decide))
    hharmonic

/-- The arbitrary-group Proposition 4.7 detector corollary. -/
theorem p47DetectorCorollary
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP47DetectorWitness
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
  apply p47DetectorCorollary_finite hqpartition hqinjective
  rw [hsorted]
  exact hdetector

end ErdosProblems.E274
