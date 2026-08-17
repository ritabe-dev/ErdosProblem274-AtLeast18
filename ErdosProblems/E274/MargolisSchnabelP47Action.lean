import ErdosProblems.E274.FiniteHarmonicCore
import Mathlib.GroupTheory.IndexNormal

/-!
# The index-three action step in Margolis--Schnabel Proposition 4.7

This file isolates the last, low-index group-action part of Proposition 4.7.
The long configuration classification from source Lemma 4.6 is kept separate.
Here the normal core of an index-three subgroup replaces informal reasoning
inside `S₃`; its quotient has order six, and subgroup images can then be
controlled by relative indices.
-/

namespace ErdosProblems.E274

open scoped Pointwise

universe u

/-- If multiplying a finite subgroup by another subgroup does not enlarge its
carrier, then the second subgroup was already contained in the first. -/
theorem subgroup_le_of_natCard_mul_eq_natCard
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G)
    (hcard : Nat.card ((U : Set G) * (V : Set G)) = Nat.card U) :
    V ≤ U := by
  have hsubset : (U : Set G) ⊆ (U : Set G) * (V : Set G) :=
    Set.subset_mul_left _ V.one_mem
  have hcardSet : ((U : Set G) * (V : Set G)).ncard = (U : Set G).ncard := by
    simpa only [Nat.card_coe_set_eq] using hcard
  have heq : (U : Set G) = (U : Set G) * (V : Set G) :=
    Set.eq_of_subset_of_ncard_le hsubset (by omega)
  intro v hv
  have hvProduct : v ∈ (U : Set G) * (V : Set G) :=
    Set.subset_mul_right _ U.one_mem hv
  rw [← heq] at hvProduct
  exact hvProduct

/-- If an index-three subgroup has a product with another subgroup occupying
exactly two thirds of a finite group, its normal core has index six. -/
theorem normalCore_index_eq_six_of_index_three_of_product_two_thirds
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G)
    (hU : U.index = 3)
    (hproduct :
      3 * Nat.card ((U : Set G) * (V : Set G)) = 2 * Nat.card G) :
    U.normalCore.index = 6 := by
  have hUfinite : U.index ≠ 0 := by omega
  letI : U.FiniteIndex := ⟨hUfinite⟩
  have hcoreDvdFactorial : U.normalCore.index ∣ Nat.factorial U.index := by
    rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker,
      Subgroup.index_eq_card, ← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card
      (MulAction.toPermHom G (G ⧸ U)).range
  have hcoreDvdSix : U.normalCore.index ∣ 6 := by
    simpa [hU] using hcoreDvdFactorial
  have hthreeDvdCore : 3 ∣ U.normalCore.index := by
    simpa [hU] using U.normalCore.index_dvd_of_le U.normalCore_le
  have hcoreNeZero : U.normalCore.index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have hcoreCases : U.normalCore.index = 3 ∨ U.normalCore.index = 6 := by
    have hcoreLe : U.normalCore.index ≤ 6 :=
      Nat.le_of_dvd (by decide) hcoreDvdSix
    omega
  rcases hcoreCases with hcoreThree | hcoreSix
  · have hrel : U.normalCore.relIndex U = 1 := by
      have hmul := U.normalCore.relIndex_mul_index U.normalCore_le
      rw [hcoreThree, hU] at hmul
      omega
    have hUleCore : U ≤ U.normalCore :=
      Subgroup.relIndex_eq_one.mp hrel
    have hcoreEq : U.normalCore = U :=
      le_antisymm U.normalCore_le hUleCore
    letI : U.Normal := by
      rw [← hcoreEq]
      infer_instance
    have hcarrier : ((U ⊔ V : Subgroup G) : Set G) =
        (U : Set G) * (V : Set G) := by
      exact Subgroup.normal_mul U V
    have hsubgroupProduct :
        3 * Nat.card (U ⊔ V : Subgroup G) = 2 * Nat.card G := by
      change 3 * Nat.card (↑((U ⊔ V : Subgroup G) : Set G)) =
        2 * Nat.card G
      rw [hcarrier]
      exact hproduct
    have hcardPositive : 0 < Nat.card (U ⊔ V : Subgroup G) :=
      Nat.card_pos
    have hcardEquation := (U ⊔ V).card_mul_index
    rw [← hcardEquation] at hsubgroupProduct
    have hcancel : Nat.card (U ⊔ V : Subgroup G) * 3 =
        Nat.card (U ⊔ V : Subgroup G) * (2 * (U ⊔ V).index) := by
      calc
        Nat.card (U ⊔ V : Subgroup G) * 3 =
            3 * Nat.card (U ⊔ V : Subgroup G) := by ac_rfl
        _ = 2 * (Nat.card (U ⊔ V : Subgroup G) * (U ⊔ V).index) :=
          hsubgroupProduct
        _ = Nat.card (U ⊔ V : Subgroup G) * (2 * (U ⊔ V).index) :=
          by ac_rfl
    have hfalse : 3 = 2 * (U ⊔ V).index :=
      Nat.mul_left_cancel (by omega) hcancel
    omega
  · exact hcoreSix

/-- In the index-six normal-core quotient of an index-three subgroup, any
subgroup whose relative product multiplier with the anchor is two has image
of order two.  This is the quotient-order calculation used for `U₂` and
`U₄` in Proposition 4.7. -/
theorem normalCore_relIndex_eq_two_of_anchor_relIndex_eq_two
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G)
    (hA : A.index = 3)
    (hcore : A.normalCore.index = 6)
    (hAB : A.relIndex B = 2) :
    A.normalCore.relIndex B = 2 := by
  let N := A.normalCore
  have hNA : N ≤ A := A.normalCore_le
  have hNrelA : N.relIndex A = 2 := by
    have hmul := N.relIndex_mul_index hNA
    change N.relIndex A * A.index = N.index at hmul
    rw [hA, hcore] at hmul
    omega
  have hfactorNe : N.relIndex A ≠ 0 := by omega
  have hfactorLe : N.relIndex (A ⊓ B) ≤ 2 := by
    rw [← hNrelA]
    exact Subgroup.relIndex_le_of_le_right inf_le_left hfactorNe
  have hmul : N.relIndex (A ⊓ B) * 2 = N.relIndex B := by
    have h := Subgroup.relIndex_inf_mul_relIndex N A B
    rw [hAB, inf_of_le_left hNA] at h
    exact h
  have hle : N.relIndex B ≤ 4 := by omega
  have heven : 2 ∣ N.relIndex B := by
    rw [← hmul]
    exact dvd_mul_left 2 _
  have hdivSix : N.relIndex B ∣ 6 := by
    rw [← hcore]
    letI : N.Normal := inferInstance
    exact Subgroup.relIndex_dvd_index_of_normal (H := N) (K := B)
  have hne : N.relIndex B ≠ 0 := by
    letI : N.IsFiniteRelIndex B :=
      Subgroup.isFiniteRelIndex_of_finiteIndex (H := N) (K := B)
    exact Subgroup.relIndex_ne_zero
  interval_cases hvalue : N.relIndex B
  all_goals try omega

/-- The final index-three-action contradiction used after the configuration
classification in Proposition 4.7.  The hypotheses record only the relative
indices and product sizes from the surviving configuration. -/
theorem indexThreeAction_configuration_impossible
    {G : Type u} [Group G] [Finite G]
    (A B C D : Subgroup G) (r : ℕ)
    (hA : A.index = 3)
    (hAB : A.relIndex B = 2)
    (hAD : A.relIndex D = 2)
    (hABCard : 3 * Nat.card ((A : Set G) * (B : Set G)) =
      2 * Nat.card G)
    (hACard : Nat.card ((A : Set G) * (C : Set G)) = Nat.card A)
    (hCDCard : 2 * Nat.card ((C : Set G) * (D : Set G)) = Nat.card G)
    (hBC : B.relIndex C = r)
    (hrOdd : Odd r) :
    False := by
  let N := A.normalCore
  have hcore : N.index = 6 :=
    normalCore_index_eq_six_of_index_three_of_product_two_thirds
      A B hA hABCard
  have hNA : N ≤ A := A.normalCore_le
  have hNrelA : N.relIndex A = 2 := by
    have hmul := N.relIndex_mul_index hNA
    change N.relIndex A * A.index = N.index at hmul
    rw [hA, hcore] at hmul
    omega
  have hNrelB : N.relIndex B = 2 :=
    normalCore_relIndex_eq_two_of_anchor_relIndex_eq_two A B hA hcore hAB
  have hNrelD : N.relIndex D = 2 :=
    normalCore_relIndex_eq_two_of_anchor_relIndex_eq_two A D hA hcore hAD
  have hCleA : C ≤ A :=
    subgroup_le_of_natCard_mul_eq_natCard A C hACard
  have hNrelCLe : N.relIndex C ≤ 2 := by
    rw [← hNrelA]
    exact Subgroup.relIndex_le_of_le_right hCleA (by omega)
  have hNrelCNeZero : N.relIndex C ≠ 0 := by
    letI : N.IsFiniteRelIndex C :=
      Subgroup.isFiniteRelIndex_of_finiteIndex (H := N) (K := C)
    exact Subgroup.relIndex_ne_zero
  have hNrelC : N.relIndex C = 2 := by
    have honeImpossible : N.relIndex C ≠ 1 := by
      intro hone
      have hCleN : C ≤ N := Subgroup.relIndex_eq_one.mp hone
      letI : N.Normal := inferInstance
      have hNrelJoin : N.relIndex (N ⊔ D) = 2 := by
        rw [Subgroup.relIndex_sup_left]
        exact hNrelD
      have hjoinIndex : (N ⊔ D).index = 3 := by
        have hmul := N.relIndex_mul_index (show N ≤ N ⊔ D from le_sup_left)
        rw [hNrelJoin, hcore] at hmul
        omega
      have hsubset : (C : Set G) * (D : Set G) ⊆ (N ⊔ D : Subgroup G) := by
        rintro x ⟨c, hc, d, hd, rfl⟩
        exact (N ⊔ D).mul_mem
          ((hCleN.trans (show N ≤ N ⊔ D from le_sup_left)) hc)
          ((show D ≤ N ⊔ D from le_sup_right) hd)
      have hcardLe : Nat.card ((C : Set G) * (D : Set G)) ≤
          Nat.card (N ⊔ D : Subgroup G) := by
        have hle := Set.ncard_le_ncard hsubset
        simpa only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] using hle
      have hjoinCard := (N ⊔ D).card_mul_index
      rw [hjoinIndex] at hjoinCard
      have hGpos : 0 < Nat.card G := Nat.card_pos
      omega
    omega
  have hNrelAB : N.relIndex (A ⊓ B) = 1 := by
    have hmul := Subgroup.relIndex_inf_mul_relIndex N A B
    rw [hAB, inf_of_le_left hNA, hNrelB] at hmul
    omega
  have hABleN : A ⊓ B ≤ N := Subgroup.relIndex_eq_one.mp hNrelAB
  have hBCleAB : B ⊓ C ≤ A ⊓ B := by
    intro x hx
    exact ⟨hCleA hx.2, hx.1⟩
  have hBCleNC : B ⊓ C ≤ N ⊓ C := by
    intro x hx
    exact ⟨hABleN (hBCleAB hx), hx.2⟩
  have hdvd : N.relIndex C ∣ B.relIndex C :=
    by
      simpa only [Subgroup.inf_relIndex_right] using
        (Subgroup.relIndex_dvd_of_le_left (L := C) hBCleNC)
  rw [hNrelC, hBC] at hdvd
  exact hrOdd.not_two_dvd_nat hdvd

end ErdosProblems.E274
