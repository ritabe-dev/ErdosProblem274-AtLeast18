import ErdosProblems.E274.MargolisSchnabelP45
import ErdosProblems.E274.ObstructionSelection
import ErdosProblems.E274.FiniteQuotientBridge

/-!
# Proposition 4.5 as an executable-detector corollary

This file selects the four cells exposed by `containsP45` and applies the
locally proved finite-group obstruction.  The arbitrary-group statement then
uses the common-normal-core finite quotient, which preserves the complete
index profile.
-/

namespace ErdosProblems.E274

universe u

/-- A Proposition 4.5 detector witness cannot occur in an exact partition of
a finite group. -/
theorem p45DetectorCorollary_finite
    {G : Type u} [Group G] [Finite G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP45DetectorWitness
      (sortedIndexList H hinjective)) : False := by
  let xs := sortedIndexList H hinjective
  rcases hdetector with ⟨r₀, hr₀, rs, hsub, hlen, hcop⟩
  have hr₀Source := twiceOddPool_mem_source hr₀
  have hrsNodup : rs.Nodup :=
    detectorResidual_nodup (sortedIndexList_nodup H hinjective) hsub
  let q : Fin 3 → ℕ := fixedLengthFamily rs hlen
  let r : Fin 4 → ℕ := ![r₀, q 0, q 1, q 2]
  let a : Fin 4 → ℕ := ![2 * r₀, 4 * q 0, 4 * q 1, 4 * q 2]
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
  have hlowNe (t : ℕ) : 2 * r₀ ≠ 4 * t := by
    intro h
    have hodd : r₀ % 2 = 1 := hr₀Source.2
    omega
  have hhighNe (t : ℕ) : 4 * t ≠ 2 * r₀ := (hlowNe t).symm
  have haInjective : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  have haMem : ∀ i, a i ∈ xs := by
    intro i
    fin_cases i
    · simpa [a, xs] using hr₀Source.1
    · simp only [a, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact scaled_mem_of_mem_divisiblePool
        (hsub.subset (fixedLengthFamily_mem rs hlen 0))
    · simp only [a, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact scaled_mem_of_mem_divisiblePool
        (hsub.subset (fixedLengthFamily_mem rs hlen 1))
    · simp only [a, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact scaled_mem_of_mem_divisiblePool
        (hsub.subset (fixedLengthFamily_mem rs hlen 2))
  let e : Fin 4 ↪ Fin n :=
    selectedIndexEmbedding H hinjective a haMem haInjective
  have hindex0 : (H (e 0)).index = 2 * r 0 := by
    simp [e, a, r, xs]
  have hindexHigh : ∀ i, i ≠ 0 → (H (e i)).index = 4 * r i := by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · simp [e, a, r, xs]
    · simp [e, a, r, xs]
    · simp [e, a, r, xs]
  have hlen4 : (r₀ :: rs).length = 4 := by simp [hlen]
  have hrCoprime : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j) := by
    have hp := fixedLengthFamily_pairwise
      (fun _ _ h ↦ h.symm) hlen4 hcop
    intro i j hij
    have hpij := hp i j hij
    fin_cases i <;> fin_cases j <;>
      simpa [r, q, fixedLengthFamily, hlen4] using hpij
  have hharmonic : IsHarmonicCosetFamily
      (fun i : Fin 4 ↦ g (e i)) (fun i : Fin 4 ↦ H (e i)) :=
    hpartition.selectedIndexFamily_harmonic
      hinjective a haMem haInjective
  exact margolisSchnabel_prop4_5_finite
    (fun i : Fin 4 ↦ g (e i)) (fun i : Fin 4 ↦ H (e i)) r
    hindex0 hindexHigh (by simpa [r] using hr₀Source.2)
    hrCoprime hharmonic

/-- The arbitrary-group Proposition 4.5 detector corollary. -/
theorem p45DetectorCorollary
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (hdetector : HasP45DetectorWitness
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
  apply p45DetectorCorollary_finite hqpartition hqinjective
  rw [hsorted]
  exact hdetector

end ErdosProblems.E274
