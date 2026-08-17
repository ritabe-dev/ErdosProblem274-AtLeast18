import ErdosProblems.E274.CommonFactorPairData
import ErdosProblems.E274.MargolisSchnabelP42
import ErdosProblems.E274.MargolisSchnabelP45
import ErdosProblems.E274.MargolisSchnabelP47Action

/-!
# Margolis--Schnabel Proposition 4.7, specialized to the index-three case

This file proves the source-shaped finite-group obstruction for indices
`(3, 3*r₂, 6*r₃, 6*r₄, 6*r₅)`.  We specialize source Lemma 4.6 at its
first residual `r₁ = 1`; this avoids formalizing configuration branches that
cannot occur in Proposition 4.7.

Two points in the printed proof are deliberately made explicit here.  First,
uses of the compressed final inference in Corollary 3.11 are replaced by an
exact mixed-triangle argument (the displayed inequality in Lemma 3.10(a)
alone does not imply the printed coprimality conclusion).  Second, the last
line of Lemma 4.6 repeats the vector `(1,2,2,3,1,1)` that is already printed
at the start of the penultimate paragraph.  Consistency with the listed
remaining cases and with the lemma statement requires that paragraph-start
occurrence to be `(1,2,2,3,3,1)`; the unique surviving vector is the final
`(1,2,2,3,1,1)`, consistently with Proposition 4.7.
-/

namespace ErdosProblems.E274

open scoped Pointwise

universe u

private theorem p47_reverseRelIndex
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) {m r s k : ℕ}
    (hU : U.index = m * r) (hV : V.index = m * s)
    (hrpos : 0 < r) (hUV : U.relIndex V = r * k) :
    V.relIndex U = s * k := by
  have hinterU : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hinterV : V.relIndex U * U.index = (U ⊓ V).index := by
    rw [inf_comm]
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := V ⊓ U) (K := U) inf_le_right)
  have hmul : (m * r) * V.relIndex U = (m * r) * (s * k) := by
    calc
      (m * r) * V.relIndex U = V.relIndex U * U.index := by rw [hU]; ring
      _ = (U ⊓ V).index := hinterV
      _ = U.relIndex V * V.index := hinterU.symm
      _ = (r * k) * (m * s) := by rw [hUV, hV]
      _ = (m * r) * (s * k) := by ring
  have hmrpos : 0 < m * r := by
    have hUne : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hU] at hUne
    omega
  exact Nat.mul_left_cancel hmrpos hmul

private theorem p47_three_mul_productCard
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) {r k : ℕ}
    (hV : V.index = 3 * r) (hVU : V.relIndex U = r * k) :
    3 * Nat.card ((U : Set G) * (V : Set G)) = k * Nat.card G := by
  have hcard := natCard_subgroup_mul U V
  have hVcard := V.card_mul_index
  rw [hVU] at hcard
  rw [hV] at hVcard
  nlinarith

private theorem p47_six_mul_productCard
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) {r k : ℕ}
    (hV : V.index = 6 * r) (hVU : V.relIndex U = r * k) :
    6 * Nat.card ((U : Set G) * (V : Set G)) = k * Nat.card G := by
  have hcard := natCard_subgroup_mul U V
  have hVcard := V.card_mul_index
  rw [hVU] at hcard
  rw [hV] at hVcard
  nlinarith

private theorem p47_harmonic3
    {G : Type u} [Group G]
    (A B C : Subgroup G) (a b c : G)
    (hAB : ∀ x, ¬(InLeftCoset a A x ∧ InLeftCoset b B x))
    (hAC : ∀ x, ¬(InLeftCoset a A x ∧ InLeftCoset c C x))
    (hBC : ∀ x, ¬(InLeftCoset b B x ∧ InLeftCoset c C x)) :
    IsHarmonicCosetFamily ![a, b, c] ![A, B, C] := by
  intro i j hij x hx
  fin_cases i <;> fin_cases j
  all_goals simp_all
  · exact hAB x hx.1 hx.2
  · exact hAC x hx.1 hx.2
  · exact hAB x hx.2 hx.1
  · exact hBC x hx.1 hx.2
  · exact hAC x hx.2 hx.1
  · exact hBC x hx.2 hx.1

private theorem p47_harmonic4
    {G : Type u} [Group G]
    (A B C D : Subgroup G) (a b c d : G)
    (hAB : ∀ x, ¬(InLeftCoset a A x ∧ InLeftCoset b B x))
    (hAC : ∀ x, ¬(InLeftCoset a A x ∧ InLeftCoset c C x))
    (hAD : ∀ x, ¬(InLeftCoset a A x ∧ InLeftCoset d D x))
    (hBC : ∀ x, ¬(InLeftCoset b B x ∧ InLeftCoset c C x))
    (hBD : ∀ x, ¬(InLeftCoset b B x ∧ InLeftCoset d D x))
    (hCD : ∀ x, ¬(InLeftCoset c C x ∧ InLeftCoset d D x)) :
    IsHarmonicCosetFamily ![a, b, c, d] ![A, B, C, D] := by
  intro i j hij x hx
  fin_cases i <;> fin_cases j
  all_goals simp_all
  · exact hAB x hx.1 hx.2
  · exact hAC x hx.1 hx.2
  · exact hAD x hx.1 hx.2
  · exact hAB x hx.2 hx.1
  · exact hBC x hx.1 hx.2
  · exact hBD x hx.1 hx.2
  · exact hAC x hx.2 hx.1
  · exact hBC x hx.2 hx.1
  · exact hCD x hx.1 hx.2
  · exact hAD x hx.2 hx.1
  · exact hBD x hx.2 hx.1
  · exact hCD x hx.2 hx.1

private theorem p47_product_subset_product_of_le_left
    {G : Type u} [Group G] (U V W : Subgroup G) (hUV : U ≤ V) :
    (U : Set G) * (W : Set G) ⊆ (V : Set G) * (W : Set G) := by
  rintro x ⟨u, hu, w, hw, rfl⟩
  exact ⟨u, hUV hu, w, hw, rfl⟩

private theorem p47_product_subset_product_of_le_right
    {G : Type u} [Group G] (U V W : Subgroup G) (hUV : U ≤ V) :
    (W : Set G) * (U : Set G) ⊆ (W : Set G) * (V : Set G) := by
  rintro x ⟨w, hw, u, hu, rfl⟩
  exact ⟨w, hw, u, hUV hu, rfl⟩

/-! ## A repaired common-factor-three mixed triangle -/

private theorem p47_tripleMultiplierData
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) {ru rv rw c : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hrvrw : Nat.Coprime rv rw)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = c * rv) :
    ∃ k : ℕ,
      W.relIndex (U ⊓ V) = rw * k ∧ 0 < k ∧ k ≤ c ∧ 2 ∣ k * rv := by
  have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hWfinite : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrupos : 0 < ru := by
    rw [hU] at hUfinite
    omega
  have hrvpos : 0 < rv := by
    rw [hV] at hVfinite
    omega
  have hrwpos : 0 < rw := by
    rw [hW] at hWfinite
    omega
  have hUVindex : (U ⊓ V).index = 3 * (ru * rv) := by
    have h := Subgroup.relIndex_mul_index
      (H := U ⊓ V) (K := V) inf_le_right
    simp only [Subgroup.inf_relIndex_right] at h
    rw [hrelUV, hV] at h
    nlinarith
  have hUWindex : (U ⊓ W).index = 3 * (2 * (ru * rw)) := by
    have h := Subgroup.relIndex_mul_index
      (H := U ⊓ W) (K := W) inf_le_right
    simp only [Subgroup.inf_relIndex_right] at h
    rw [hrelUW, hW] at h
    nlinarith
  have htripleIndex :
      W.relIndex (U ⊓ V) * (U ⊓ V).index =
        (W ⊓ (U ⊓ V)).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index
        (H := W ⊓ (U ⊓ V)) (K := U ⊓ V) inf_le_right)
  have htripleLe : W ⊓ (U ⊓ V) ≤ U ⊓ W := by
    intro x hx
    exact ⟨hx.2.1, hx.1⟩
  have hraw : (U ⊓ W).index ∣ (W ⊓ (U ⊓ V)).index :=
    Subgroup.index_dvd_of_le htripleLe
  have hfactor :
      (3 * ru) * (2 * rw) ∣
        (3 * ru) * (W.relIndex (U ⊓ V) * rv) := by
    rw [hUWindex, ← htripleIndex, hUVindex] at hraw
    simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
  have hcancel : 2 * rw ∣ W.relIndex (U ⊓ V) * rv :=
    Nat.dvd_of_mul_dvd_mul_left (by omega) hfactor
  have hrwDivProduct : rw ∣ W.relIndex (U ⊓ V) * rv :=
    (show rw ∣ 2 * rw by exact ⟨2, by omega⟩).trans hcancel
  have hrwDiv : rw ∣ W.relIndex (U ⊓ V) :=
    hrvrw.symm.dvd_of_dvd_mul_right hrwDivProduct
  rcases hrwDiv with ⟨k, hk⟩
  have hrelTripleNe : W.relIndex (U ⊓ V) ≠ 0 := by
    intro hzero
    exact hWfinite (W.index_eq_zero_of_relIndex_eq_zero hzero)
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := Nat.eq_zero_of_not_pos h
    exact hrelTripleNe (by simpa [this] using hk)
  have hrevVW : W.relIndex V = c * rw := by
    simpa [mul_comm] using
      (p47_reverseRelIndex V W (m := 3) (r := rv) (s := rw) (k := c)
        hV hW hrvpos (by simpa [mul_comm] using hrelVW))
  have hrelWVNe : W.relIndex V ≠ 0 := by
    intro hzero
    exact hWfinite (W.index_eq_zero_of_relIndex_eq_zero hzero)
  have hupper : W.relIndex (U ⊓ V) ≤ W.relIndex V :=
    Subgroup.relIndex_le_of_le_right inf_le_right hrelWVNe
  have hkle : k ≤ c := by
    rw [hk, hrevVW] at hupper
    nlinarith
  have htwo : 2 ∣ k * rv := by
    have hcancel' : rw * 2 ∣ rw * (k * rv) := by
      simpa [hk, mul_assoc, mul_left_comm, mul_comm] using hcancel
    exact Nat.dvd_of_mul_dvd_mul_left hrwpos hcancel'
  exact ⟨k, hk, hkpos, hkle, htwo⟩

private theorem p47_evenMiddleOfOneTwoOne
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hrvrw : Nat.Coprime rv rw)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = rv) : Even rv := by
  rcases p47_tripleMultiplierData (c := 1) U V W hU hV hW hrvrw
      hrelUV hrelUW (by simpa using hrelVW) with
    ⟨k, -, hkpos, hkle, htwo⟩
  have hk : k = 1 := by omega
  rw [hk, one_mul] at htwo
  exact even_iff_two_dvd.mpr htwo

private theorem p47_tripleRelIndexEqTwoOfOddMiddle
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hrvrw : Nat.Coprime rv rw)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = 2 * rv)
    (hrvOdd : ¬ Even rv) :
    W.relIndex (U ⊓ V) = 2 * rw := by
  rcases p47_tripleMultiplierData U V W hU hV hW hrvrw
      hrelUV hrelUW hrelVW with
    ⟨k, hk, hkpos, hkle, htwo⟩
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl
  · exact False.elim (hrvOdd (even_iff_two_dvd.mpr (by simpa using htwo)))
  · simpa [mul_comm] using hk

private theorem p47_infMulEqOfOneTwoTwoOddMiddle
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hrvrw : Nat.Coprime rv rw)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = 2 * rv)
    (hrvOdd : ¬ Even rv) :
    ((U ⊓ V : Subgroup G) : Set G) * (W : Set G) =
      (V : Set G) * (W : Set G) := by
  have htriple := p47_tripleRelIndexEqTwoOfOddMiddle
    U V W hU hV hW hrvrw hrelUV hrelUW hrelVW hrvOdd
  have hrvpos : 0 < rv := by
    have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hV] at hVfinite
    omega
  have hrevVW : W.relIndex V = 2 * rw := by
    simpa [mul_comm] using
      (p47_reverseRelIndex V W (m := 3) (r := rv) (s := rw) (k := 2)
        hV hW hrvpos (by simpa [mul_comm] using hrelVW))
  have hsubset : ((U ⊓ V : Subgroup G) : Set G) * (W : Set G) ⊆
      (V : Set G) * (W : Set G) := by
    rintro x ⟨z, hz, w, hw, rfl⟩
    exact ⟨z, hz.2, w, hw, rfl⟩
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    natCard_subgroup_mul, natCard_subgroup_mul, htriple, hrevVW]

private theorem p47_noOneTwoTwoOfOddMiddle
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hrvrw : Nat.Coprime rv rw)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = 2 * rv)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x))
    (hrvOdd : ¬ Even rv) : False := by
  have hrvpos : 0 < rv := by
    have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hV] at hVfinite
    omega
  have hruPos : 0 < ru := by
    have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hU] at hUfinite
    omega
  have heq := p47_infMulEqOfOneTwoTwoOddMiddle
    U V W hU hV hW hrvrw hrelUV hrelUW hrelVW hrvOdd
  have hsubset : (V : Set G) * (W : Set G) ⊆
      (U : Set G) * (W : Set G) := by
    rw [← heq]
    rintro x ⟨z, hz, w, hw, rfl⟩
    exact ⟨z, hz.1, w, hw, rfl⟩
  have hrevUV : V.relIndex U = rv := by
    simpa using (p47_reverseRelIndex U V (k := 1)
      hU hV hruPos (by simpa using hrelUV))
  have hcardWV := p47_three_mul_productCard W V (r := rv) (k := 2)
    hV (by simpa [mul_comm] using hrelVW)
  have hcardUV := p47_three_mul_productCard U V (k := 1) hV
    (by simpa using hrevUV)
  have hcard : Nat.card G ≤
      Nat.card ((W : Set G) * (V : Set G)) +
        Nat.card ((U : Set G) * (V : Set G)) := by omega
  exact not_harmonic_three_of_product_cover W U V c a b
    (fun x hx ↦ hUW x ⟨hx.2, hx.1⟩)
    (fun x hx ↦ hVW x ⟨hx.2, hx.1⟩) hUV hsubset hcard

private theorem p47_noOneTwoTwo
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hruv : Nat.Coprime ru rv) (hruw : Nat.Coprime ru rw)
    (hrvrw : Nat.Coprime rv rw)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = 2 * rv)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x)) : False := by
  by_cases hrvEven : Even rv
  · have hruOdd : ¬ Even ru := by
      intro hruEven
      have htwoGcd : 2 ∣ Nat.gcd ru rv :=
        Nat.dvd_gcd hruEven.two_dvd hrvEven.two_dvd
      rw [hruv.gcd_eq_one] at htwoGcd
      norm_num at htwoGcd
    have hruPos : 0 < ru := by
      have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rw [hU] at hUfinite
      omega
    have hrevUV : V.relIndex U = rv := by
      simpa using (p47_reverseRelIndex U V (k := 1)
        hU hV hruPos (by simpa using hrelUV))
    exact p47_noOneTwoTwoOfOddMiddle V U W b a c hV hU hW
      hruw hrevUV hrelVW hrelUW
      (fun x hx ↦ hUV x ⟨hx.2, hx.1⟩) hVW hUW hruOdd
  · exact p47_noOneTwoTwoOfOddMiddle U V W a b c hU hV hW
      hrvrw hrelUV hrelUW hrelVW hUV hUW hVW hrvEven

/-! ## The index-three pigeonhole used in specialized Claim 1 -/

private theorem p47_quotient_eq_of_avoids_two
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (hA : A.index = 3)
    (q₀ q₁ q₂ q₃ : G ⧸ A)
    (h₀₁ : q₀ ≠ q₁)
    (h₂₀ : q₂ ≠ q₀) (h₂₁ : q₂ ≠ q₁)
    (h₃₀ : q₃ ≠ q₀) (h₃₁ : q₃ ≠ q₁) : q₂ = q₃ := by
  classical
  by_contra h₂₃
  have hAne : A.index ≠ 0 := by omega
  letI : Fintype (G ⧸ A) := A.fintypeOfIndexNeZero hAne
  let f : Fin 4 → G ⧸ A := ![q₀, q₁, q₂, q₃]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hcard := Fintype.card_le_of_injective f hf
  have hquotCard : Fintype.card (G ⧸ A) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← A.index_eq_card, hA]
  rw [hquotCard] at hcard
  norm_num at hcard

private theorem p47_product_eq_anchor_of_third_multiplier_one
    {G : Type u} [Group G] [Finite G]
    (A U V : Subgroup G)
    (hA : A.index = 3) (hUle : U ≤ A) (hVle : V ≤ A)
    (hcard : 3 * Nat.card ((U : Set G) * (V : Set G)) = Nat.card G) :
    (U : Set G) * (V : Set G) = A := by
  have hsubset : (U : Set G) * (V : Set G) ⊆ A := by
    rintro x ⟨u, hu, v, hv, rfl⟩
    exact A.mul_mem (hUle hu) (hVle hv)
  apply Set.eq_of_subset_of_ncard_le hsubset
  have hAcard := A.card_mul_index
  rw [hA] at hAcard
  simpa only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] using
    (show Nat.card A ≤ Nat.card ((U : Set G) * (V : Set G)) by omega)

private theorem p47_quotient_ne_of_disjoint_subgroups_in_anchor
    {G : Type u} [Group G]
    (A U V : Subgroup G) (a b : G)
    (hprod : (U : Set G) * (V : Set G) = A)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    (QuotientGroup.mk a : G ⧸ A) ≠ QuotientGroup.mk b := by
  intro heq
  have habA : a⁻¹ * b ∈ A := by
    rw [← QuotientGroup.eq]
    exact heq
  change a⁻¹ * b ∈ (A : Set G) at habA
  rw [← hprod] at habA
  exact hdisjoint _ (leftCosets_intersect_of_inv_mul_mem_mul U V a b habA).choose_spec

private theorem p47_quotient_ne_anchor_cell
    {G : Type u} [Group G]
    (A U : Subgroup G) (a b : G)
    (hdisjoint : ∀ x, ¬(InLeftCoset a A x ∧ InLeftCoset b U x)) :
    (QuotientGroup.mk b : G ⧸ A) ≠ QuotientGroup.mk a := by
  intro heq
  have hba : InLeftCoset a A b := by
    rw [InLeftCoset, ← QuotientGroup.eq]
    exact heq.symm
  exact hdisjoint b ⟨hba, by simp [InLeftCoset]⟩

private theorem p47_p42_inside_anchor
    {G : Type u} [Group G] [Finite G]
    (A X Y Z : Subgroup G) (x y z : G) (rx ry rz : ℕ)
    (hXrel : X.relIndex A = 2 * rx)
    (hYrel : Y.relIndex A = 2 * ry)
    (hZrel : Z.relIndex A = 2 * rz)
    (hxyQ : (QuotientGroup.mk x : G ⧸ A) = QuotientGroup.mk y)
    (hxzQ : (QuotientGroup.mk x : G ⧸ A) = QuotientGroup.mk z)
    (hxy : ∀ t, ¬(InLeftCoset x X t ∧ InLeftCoset y Y t))
    (hxz : ∀ t, ¬(InLeftCoset x X t ∧ InLeftCoset z Z t))
    (hyz : ∀ t, ¬(InLeftCoset y Y t ∧ InLeftCoset z Z t))
    (hcxy : Nat.Coprime rx ry) (hcxz : Nat.Coprime rx rz)
    (hcyz : Nat.Coprime ry rz) : False := by
  have hyA : x⁻¹ * y ∈ A := by
    rw [← QuotientGroup.eq]
    exact hxyQ
  have hzA : x⁻¹ * z ∈ A := by
    rw [← QuotientGroup.eq]
    exact hxzQ
  let ay : A := ⟨x⁻¹ * y, hyA⟩
  let az : A := ⟨x⁻¹ * z, hzA⟩
  let XA : Subgroup A := X.subgroupOf A
  let YA : Subgroup A := Y.subgroupOf A
  let ZA : Subgroup A := Z.subgroupOf A
  have hXA : XA.index = 2 * rx := by
    change X.relIndex A = 2 * rx
    exact hXrel
  have hYA : YA.index = 2 * ry := by
    change Y.relIndex A = 2 * ry
    exact hYrel
  have hZA : ZA.index = 2 * rz := by
    change Z.relIndex A = 2 * rz
    exact hZrel
  have hdXY : ∀ t : A,
      ¬(InLeftCoset (1 : A) XA t ∧ InLeftCoset ay YA t) := by
    intro t ht
    apply hxy (x * (t : G))
    constructor
    · simpa [InLeftCoset, XA] using ht.1
    · have hty := ht.2
      change (ay⁻¹ * t : A) ∈ YA at hty
      change (((ay⁻¹ * t : A) : A) : G) ∈ Y at hty
      simpa [ay, mul_assoc] using hty
  have hdXZ : ∀ t : A,
      ¬(InLeftCoset (1 : A) XA t ∧ InLeftCoset az ZA t) := by
    intro t ht
    apply hxz (x * (t : G))
    constructor
    · simpa [InLeftCoset, XA] using ht.1
    · have htz := ht.2
      change (az⁻¹ * t : A) ∈ ZA at htz
      change (((az⁻¹ * t : A) : A) : G) ∈ Z at htz
      simpa [az, mul_assoc] using htz
  have hdYZ : ∀ t : A,
      ¬(InLeftCoset ay YA t ∧ InLeftCoset az ZA t) := by
    intro t ht
    apply hyz (x * (t : G))
    constructor
    · have hty := ht.1
      change (ay⁻¹ * t : A) ∈ YA at hty
      change (((ay⁻¹ * t : A) : A) : G) ∈ Y at hty
      simpa [ay, mul_assoc] using hty
    · have htz := ht.2
      change (az⁻¹ * t : A) ∈ ZA at htz
      change (((az⁻¹ * t : A) : A) : G) ∈ Z at htz
      simpa [az, mul_assoc] using htz
  exact margolisSchnabelP42 XA YA ZA 1 ay az rx ry rz
    hXA hYA hZA hcxy hcxz hcyz (p47_harmonic3 XA YA ZA 1 ay az hdXY hdXZ hdYZ)

private theorem p47_anchorPairMultiplierOne_impossible
    {G : Type u} [Group G] [Finite G]
    (A B C D E : Subgroup G) (a b c d e : G)
    (r₂ r₃ r₄ r₅ : ℕ)
    (hA : A.index = 3)
    (hB : B.index = 3 * r₂)
    (hC : C.index = 6 * r₃)
    (hD : D.index = 6 * r₄)
    (hE : E.index = 6 * r₅)
    (hc₃₄ : Nat.Coprime r₃ r₄)
    (hc₃₅ : Nat.Coprime r₃ r₅)
    (hc₄₅ : Nat.Coprime r₄ r₅)
    (hAB : A.relIndex B = 1)
    (hAC : A.relIndex C = 1) (hAD : A.relIndex D = 1)
    (hAE : A.relIndex E = 1)
    (hCA : C.relIndex A = 2 * r₃)
    (hDA : D.relIndex A = 2 * r₄)
    (hEA : E.relIndex A = 2 * r₅)
    (hCB : C.relIndex B = 2 * r₃)
    (hDB : D.relIndex B = 2 * r₄)
    (hEB : E.relIndex B = 2 * r₅)
    (hh : IsHarmonicCosetFamily ![a, b, c, d, e] ![A, B, C, D, E]) :
    False := by
  have hdAB := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hdAC := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdAD := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdAE := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdBC := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdBD := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdBE := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdCD := hh (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdCE := hh (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdDE := hh (i := (3 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hdAB hdAC hdAD hdAE hdBC hdBD hdBE hdCD hdCE hdDE
  have hBle : B ≤ A := Subgroup.relIndex_eq_one.mp hAB
  have hCle : C ≤ A := Subgroup.relIndex_eq_one.mp hAC
  have hDle : D ≤ A := Subgroup.relIndex_eq_one.mp hAD
  have hEle : E ≤ A := Subgroup.relIndex_eq_one.mp hAE
  have hC3 : C.index = 3 * (2 * r₃) := by omega
  have hD3 : D.index = 3 * (2 * r₄) := by omega
  have hE3 : E.index = 3 * (2 * r₅) := by omega
  have hcardBC : 3 * Nat.card ((B : Set G) * (C : Set G)) = Nat.card G := by
    have h := p47_three_mul_productCard B C (r := 2 * r₃) (k := 1)
      hC3 (by simpa using hCB)
    simpa using h
  have hcardBD : 3 * Nat.card ((B : Set G) * (D : Set G)) = Nat.card G := by
    have h := p47_three_mul_productCard B D (r := 2 * r₄) (k := 1)
      hD3 (by simpa using hDB)
    simpa using h
  have hcardBE : 3 * Nat.card ((B : Set G) * (E : Set G)) = Nat.card G := by
    have h := p47_three_mul_productCard B E (r := 2 * r₅) (k := 1)
      hE3 (by simpa using hEB)
    simpa using h
  have hprodBC : (B : Set G) * (C : Set G) = A :=
    p47_product_eq_anchor_of_third_multiplier_one A B C hA hBle hCle hcardBC
  have hprodBD : (B : Set G) * (D : Set G) = A :=
    p47_product_eq_anchor_of_third_multiplier_one A B D hA hBle hDle hcardBD
  have hprodBE : (B : Set G) * (E : Set G) = A :=
    p47_product_eq_anchor_of_third_multiplier_one A B E hA hBle hEle hcardBE
  let qa : G ⧸ A := QuotientGroup.mk a
  let qb : G ⧸ A := QuotientGroup.mk b
  let qc : G ⧸ A := QuotientGroup.mk c
  let qd : G ⧸ A := QuotientGroup.mk d
  let qe : G ⧸ A := QuotientGroup.mk e
  have hba : qb ≠ qa := p47_quotient_ne_anchor_cell A B a b
    (fun x hx ↦ hdAB x hx.1 hx.2)
  have hca : qc ≠ qa := p47_quotient_ne_anchor_cell A C a c
    (fun x hx ↦ hdAC x hx.1 hx.2)
  have hda : qd ≠ qa := p47_quotient_ne_anchor_cell A D a d
    (fun x hx ↦ hdAD x hx.1 hx.2)
  have hea : qe ≠ qa := p47_quotient_ne_anchor_cell A E a e
    (fun x hx ↦ hdAE x hx.1 hx.2)
  have hbc : qb ≠ qc := p47_quotient_ne_of_disjoint_subgroups_in_anchor
    A B C b c hprodBC (fun x hx ↦ hdBC x hx.1 hx.2)
  have hbd : qb ≠ qd := p47_quotient_ne_of_disjoint_subgroups_in_anchor
    A B D b d hprodBD (fun x hx ↦ hdBD x hx.1 hx.2)
  have hbe : qb ≠ qe := p47_quotient_ne_of_disjoint_subgroups_in_anchor
    A B E b e hprodBE (fun x hx ↦ hdBE x hx.1 hx.2)
  have hcdQ : qc = qd := p47_quotient_eq_of_avoids_two A hA qa qb qc qd
    hba.symm hca hbc.symm hda hbd.symm
  have hceQ : qc = qe := p47_quotient_eq_of_avoids_two A hA qa qb qc qe
    hba.symm hca hbc.symm hea hbe.symm
  exact p47_p42_inside_anchor A C D E c d e r₃ r₄ r₅
    hCA hDA hEA hcdQ hceQ
    (fun x hx ↦ hdCD x hx.1 hx.2)
    (fun x hx ↦ hdCE x hx.1 hx.2)
    (fun x hx ↦ hdDE x hx.1 hx.2)
    hc₃₄ hc₃₅ hc₄₅

private theorem p47_lowTriangle_bothOne_of_anchorPairOne
    {G : Type u} [Group G] [Finite G]
    (A B X : Subgroup G) (a b x : G) (r₂ rx kA kB : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hX : X.index = 6 * rx)
    (hodd₂ : Odd r₂) (hc₂x : Nat.Coprime r₂ rx)
    (hkApos : 0 < kA) (hkAlt : kA < 3)
    (hkBpos : 0 < kB) (hkBlt : kB < 3)
    (hAB : A.relIndex B = 1)
    (hAX : A.relIndex X = kA)
    (hXA : X.relIndex A = (2 * rx) * kA)
    (hBX : B.relIndex X = r₂ * kB)
    (hXB : X.relIndex B = (2 * rx) * kB)
    (hdAB : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset b B t))
    (hdAX : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset x X t))
    (hdBX : ∀ t, ¬(InLeftCoset b B t ∧ InLeftCoset x X t)) :
    kA = 1 ∧ kB = 1 := by
  have hA3 : A.index = 3 * 1 := by simpa using hA
  have hX3 : X.index = 3 * (2 * rx) := by omega
  have hc₂2x : Nat.Coprime r₂ (2 * rx) :=
    hodd₂.coprime_two_right.mul_right hc₂x
  have hkAcases : kA = 1 ∨ kA = 2 := by omega
  have hkBcases : kB = 1 ∨ kB = 2 := by omega
  rcases hkAcases with rfl | rfl
  · rcases hkBcases with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · have hEvenOne : Even 1 := p47_evenMiddleOfOneTwoOne X A B
        hX3 hA3 hB (by simp) (by simpa using hXA)
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using hXB)
        (by simpa using hAB)
      norm_num at hEvenOne
  · rcases hkBcases with rfl | rfl
    · have hEven₂ : Even r₂ := p47_evenMiddleOfOneTwoOne A B X
        hA3 hB hX3 hc₂2x (by simpa using hAB)
        (by simpa using hAX) (by simpa using hBX)
      exact False.elim ((Nat.not_even_iff_odd.mpr hodd₂) hEven₂)
    · exact False.elim (p47_noOneTwoTwo A B X a b x
        hA3 hB hX3 (by simp) (by simp) hc₂2x
        (by simpa using hAB) (by simpa using hAX)
        (by simpa [mul_comm] using hBX)
        hdAB hdAX hdBX)

private theorem p47_lowTriangle_equal_of_anchorPairTwo
    {G : Type u} [Group G] [Finite G]
    (A B X : Subgroup G) (a b x : G) (r₂ rx kA kB : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hX : X.index = 6 * rx)
    (hodd₂ : Odd r₂) (hc₂x : Nat.Coprime r₂ rx)
    (hkApos : 0 < kA) (hkAlt : kA < 3)
    (hkBpos : 0 < kB) (hkBlt : kB < 3)
    (hAB : A.relIndex B = 2)
    (hBA : B.relIndex A = r₂ * 2)
    (hAX : A.relIndex X = kA)
    (hXA : X.relIndex A = (2 * rx) * kA)
    (hBX : B.relIndex X = r₂ * kB)
    (hXB : X.relIndex B = (2 * rx) * kB)
    (hdAB : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset b B t))
    (hdAX : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset x X t))
    (hdBX : ∀ t, ¬(InLeftCoset b B t ∧ InLeftCoset x X t)) :
    kA = kB := by
  have hA3 : A.index = 3 * 1 := by simpa using hA
  have hX3 : X.index = 3 * (2 * rx) := by omega
  have hc₂2x : Nat.Coprime r₂ (2 * rx) :=
    hodd₂.coprime_two_right.mul_right hc₂x
  have hkAcases : kA = 1 ∨ kA = 2 := by omega
  have hkBcases : kB = 1 ∨ kB = 2 := by omega
  rcases hkAcases with rfl | rfl
  · rcases hkBcases with rfl | rfl
    · rfl
    · exact False.elim (p47_noOneTwoTwo A X B a x b
        hA3 hX3 hB (by simp) (by simp) hc₂2x.symm
        (by simpa using hAX) (by simpa using hAB)
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using hXB)
        hdAX hdAB (fun t ht ↦ hdBX t ⟨ht.2, ht.1⟩))
  · rcases hkBcases with rfl | rfl
    · exact False.elim (p47_noOneTwoTwo B X A b x a
        hB hX3 hA3 hc₂2x (by simp) (by simp)
        (by simpa using hBX) (by simpa [mul_comm] using hBA)
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using hXA)
        hdBX (fun t ht ↦ hdAB t ⟨ht.2, ht.1⟩)
        (fun t ht ↦ hdAX t ⟨ht.2, ht.1⟩))
    · rfl

private theorem p47_claim1_specialized
    {G : Type u} [Group G] [Finite G]
    (A B C D E : Subgroup G) (a b c d e : G)
    (r₂ r₃ r₄ r₅ : ℕ) (kAB kAC kAD kAE kBC kBD kBE : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hC : C.index = 6 * r₃) (hD : D.index = 6 * r₄)
    (hE : E.index = 6 * r₅)
    (hodd₂ : Odd r₂)
    (hc₂₃ : Nat.Coprime r₂ r₃) (hc₂₄ : Nat.Coprime r₂ r₄)
    (hc₂₅ : Nat.Coprime r₂ r₅) (hc₃₄ : Nat.Coprime r₃ r₄)
    (hc₃₅ : Nat.Coprime r₃ r₅) (hc₄₅ : Nat.Coprime r₄ r₅)
    (hkABpos : 0 < kAB) (hkABlt : kAB < 3)
    (hkACpos : 0 < kAC) (hkAClt : kAC < 3)
    (hkADpos : 0 < kAD) (hkADlt : kAD < 3)
    (hkAEpos : 0 < kAE) (hkAElt : kAE < 3)
    (hkBCpos : 0 < kBC) (hkBClt : kBC < 3)
    (hkBDpos : 0 < kBD) (hkBDlt : kBD < 3)
    (hkBEpos : 0 < kBE) (hkBElt : kBE < 3)
    (hAB : A.relIndex B = kAB) (hBA : B.relIndex A = r₂ * kAB)
    (hAC : A.relIndex C = kAC) (hCA : C.relIndex A = (2 * r₃) * kAC)
    (hAD : A.relIndex D = kAD) (hDA : D.relIndex A = (2 * r₄) * kAD)
    (hAE : A.relIndex E = kAE) (hEA : E.relIndex A = (2 * r₅) * kAE)
    (hBC : B.relIndex C = r₂ * kBC)
    (hCB : C.relIndex B = (2 * r₃) * kBC)
    (hBD : B.relIndex D = r₂ * kBD)
    (hDB : D.relIndex B = (2 * r₄) * kBD)
    (hBE : B.relIndex E = r₂ * kBE)
    (hEB : E.relIndex B = (2 * r₅) * kBE)
    (hh : IsHarmonicCosetFamily ![a, b, c, d, e] ![A, B, C, D, E]) :
    kAB = 2 ∧ kAC = kBC ∧ kAD = kBD ∧ kAE = kBE := by
  have hdAB := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hdAC := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdAD := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdAE := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdBC := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdBD := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdBE := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hdAB hdAC hdAD hdAE hdBC hdBD hdBE
  have hkABcases : kAB = 1 ∨ kAB = 2 := by omega
  rcases hkABcases with hkAB | hkAB
  · have hCone := p47_lowTriangle_bothOne_of_anchorPairOne
      A B C a b c r₂ r₃ kAC kBC hA hB hC hodd₂ hc₂₃
      hkACpos hkAClt hkBCpos hkBClt
      (by simpa [hkAB] using hAB) hAC hCA hBC hCB
      (fun x hx ↦ hdAB x hx.1 hx.2)
      (fun x hx ↦ hdAC x hx.1 hx.2)
      (fun x hx ↦ hdBC x hx.1 hx.2)
    have hDone := p47_lowTriangle_bothOne_of_anchorPairOne
      A B D a b d r₂ r₄ kAD kBD hA hB hD hodd₂ hc₂₄
      hkADpos hkADlt hkBDpos hkBDlt
      (by simpa [hkAB] using hAB) hAD hDA hBD hDB
      (fun x hx ↦ hdAB x hx.1 hx.2)
      (fun x hx ↦ hdAD x hx.1 hx.2)
      (fun x hx ↦ hdBD x hx.1 hx.2)
    have hEone := p47_lowTriangle_bothOne_of_anchorPairOne
      A B E a b e r₂ r₅ kAE kBE hA hB hE hodd₂ hc₂₅
      hkAEpos hkAElt hkBEpos hkBElt
      (by simpa [hkAB] using hAB) hAE hEA hBE hEB
      (fun x hx ↦ hdAB x hx.1 hx.2)
      (fun x hx ↦ hdAE x hx.1 hx.2)
      (fun x hx ↦ hdBE x hx.1 hx.2)
    rcases hCone with ⟨rfl, rfl⟩
    rcases hDone with ⟨rfl, rfl⟩
    rcases hEone with ⟨rfl, rfl⟩
    exact False.elim (p47_anchorPairMultiplierOne_impossible
      A B C D E a b c d e r₂ r₃ r₄ r₅ hA hB hC hD hE
      hc₃₄ hc₃₅ hc₄₅ (by simpa [hkAB] using hAB)
      (by simpa using hAC) (by simpa using hAD) (by simpa using hAE)
      (by simpa using hCA) (by simpa using hDA) (by simpa using hEA)
      (by simpa using hCB) (by simpa using hDB) (by simpa using hEB) hh)
  · have hCequal := p47_lowTriangle_equal_of_anchorPairTwo
      A B C a b c r₂ r₃ kAC kBC hA hB hC hodd₂ hc₂₃
      hkACpos hkAClt hkBCpos hkBClt
      (by simpa [hkAB] using hAB) (by simpa [hkAB] using hBA)
      hAC hCA hBC hCB
      (fun x hx ↦ hdAB x hx.1 hx.2)
      (fun x hx ↦ hdAC x hx.1 hx.2)
      (fun x hx ↦ hdBC x hx.1 hx.2)
    have hDequal := p47_lowTriangle_equal_of_anchorPairTwo
      A B D a b d r₂ r₄ kAD kBD hA hB hD hodd₂ hc₂₄
      hkADpos hkADlt hkBDpos hkBDlt
      (by simpa [hkAB] using hAB) (by simpa [hkAB] using hBA)
      hAD hDA hBD hDB
      (fun x hx ↦ hdAB x hx.1 hx.2)
      (fun x hx ↦ hdAD x hx.1 hx.2)
      (fun x hx ↦ hdBD x hx.1 hx.2)
    have hEequal := p47_lowTriangle_equal_of_anchorPairTwo
      A B E a b e r₂ r₅ kAE kBE hA hB hE hodd₂ hc₂₅
      hkAEpos hkAElt hkBEpos hkBElt
      (by simpa [hkAB] using hAB) (by simpa [hkAB] using hBA)
      hAE hEA hBE hEB
      (fun x hx ↦ hdAB x hx.1 hx.2)
      (fun x hx ↦ hdAE x hx.1 hx.2)
      (fun x hx ↦ hdBE x hx.1 hx.2)
    exact ⟨hkAB, hCequal, hDequal, hEequal⟩

/-! ## Fixed-size Lemma 3.5 -/

private theorem p47_thickenedDisjoint
    {G : Type u} [Group G]
    (Ui Uj V : Subgroup G) (gi gj gv : G)
    (hij : ∀ x, ¬(InLeftCoset gi Ui x ∧ InLeftCoset gj Uj x))
    (hiV : ∀ x, ¬(InLeftCoset gi Ui x ∧ InLeftCoset gv V x))
    (hjV : ∀ x, ¬(InLeftCoset gj Uj x ∧ InLeftCoset gv V x))
    (hsubset : (V : Set G) * (Ui : Set G) ⊆
      (Uj : Set G) * (Ui : Set G)) :
    Disjoint (gi • ((Ui : Set G) * (V : Set G)))
      (gj • ((Uj : Set G) * (V : Set G))) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases hxi with ⟨yi, ⟨ui, hui, v, hv, rfl⟩, hi⟩
  rcases hxj with ⟨yj, ⟨uj, huj, v', hv', rfl⟩, hj⟩
  have hsmall : (v' * v⁻¹) * ui⁻¹ ∈
      (V : Set G) * (Ui : Set G) :=
    ⟨v' * v⁻¹, V.mul_mem hv' (V.inv_mem hv),
      ui⁻¹, Ui.inv_mem hui, rfl⟩
  rcases hsubset hsmall with ⟨uj', huj', ui', hui', heqSmall⟩
  have hnot := inv_mul_notMem_mul_of_disjoint_leftCosets Uj Ui gj gi
    (fun z hz ↦ hij z ⟨hz.2, hz.1⟩)
  apply hnot
  refine ⟨uj * uj', Uj.mul_mem huj huj', ui', hui', ?_⟩
  have heq : gi * (ui * v) = gj * (uj * v') := hi.trans hj.symm
  have hji : gj⁻¹ * gi = uj * ((v' * v⁻¹) * ui⁻¹) := by
    have heq' := congrArg (fun z ↦ gj⁻¹ * z * v⁻¹ * ui⁻¹) heq
    simpa [mul_assoc] using heq'
  calc
    (uj * uj') * ui' = uj * (uj' * ui') := by simp [mul_assoc]
    _ = uj * ((v' * v⁻¹) * ui⁻¹) :=
      congrArg (fun z ↦ uj * z) heqSmall
    _ = gj⁻¹ * gi := hji.symm

private theorem p47_lemma35_three
    {G : Type u} [Group G] [Finite G]
    (U₀ U₁ U₂ V : Subgroup G) (g₀ g₁ g₂ gv : G)
    (hh : IsHarmonicCosetFamily ![g₀, g₁, g₂, gv] ![U₀, U₁, U₂, V])
    (hsub01 : (V : Set G) * (U₀ : Set G) ⊆
      (U₁ : Set G) * (U₀ : Set G))
    (hsub02 : (V : Set G) * (U₀ : Set G) ⊆
      (U₂ : Set G) * (U₀ : Set G))
    (hsub12 : (V : Set G) * (U₁ : Set G) ⊆
      (U₂ : Set G) * (U₁ : Set G))
    (hcover : Nat.card G ≤
      Nat.card ((U₀ : Set G) * (V : Set G)) +
      Nat.card ((U₁ : Set G) * (V : Set G)) +
      Nat.card ((U₂ : Set G) * (V : Set G))) : False := by
  classical
  have hd01 := hh (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  have hd02 := hh (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd0v := hh (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd12 := hh (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd1v := hh (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd2v := hh (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  simp at hd01 hd02 hd0v hd12 hd1v hd2v
  let S₀ : Set G := g₀ • ((U₀ : Set G) * (V : Set G))
  let S₁ : Set G := g₁ • ((U₁ : Set G) * (V : Set G))
  let S₂ : Set G := g₂ • ((U₂ : Set G) * (V : Set G))
  have hdS01 : Disjoint S₀ S₁ := p47_thickenedDisjoint U₀ U₁ V g₀ g₁ gv
    (fun x hx ↦ hd01 x hx.1 hx.2)
    (fun x hx ↦ hd0v x hx.1 hx.2)
    (fun x hx ↦ hd1v x hx.1 hx.2) hsub01
  have hdS02 : Disjoint S₀ S₂ := p47_thickenedDisjoint U₀ U₂ V g₀ g₂ gv
    (fun x hx ↦ hd02 x hx.1 hx.2)
    (fun x hx ↦ hd0v x hx.1 hx.2)
    (fun x hx ↦ hd2v x hx.1 hx.2) hsub02
  have hdS12 : Disjoint S₁ S₂ := p47_thickenedDisjoint U₁ U₂ V g₁ g₂ gv
    (fun x hx ↦ hd12 x hx.1 hx.2)
    (fun x hx ↦ hd1v x hx.1 hx.2)
    (fun x hx ↦ hd2v x hx.1 hx.2) hsub12
  have hdUnion : Disjoint (S₀ ∪ S₁) S₂ :=
    Set.disjoint_union_left.2 ⟨hdS02, hdS12⟩
  have hcardLower : Nat.card G ≤ ((S₀ ∪ S₁) ∪ S₂).ncard := by
    rw [Set.ncard_union_eq hdUnion, Set.ncard_union_eq hdS01]
    simp only [S₀, S₁, S₂, Set.ncard_smul_set]
    simpa only [Nat.card_coe_set_eq] using hcover
  have hfull : (S₀ ∪ S₁) ∪ S₂ = Set.univ := by
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by simpa using hcardLower)
  have hgv : gv ∈ (S₀ ∪ S₁) ∪ S₂ := by rw [hfull]; trivial
  rcases hgv with (hgv | hgv) | hgv
  · apply inv_mul_notMem_mul_of_disjoint_leftCosets U₀ V g₀ gv
      (fun x hx ↦ hd0v x hx.1 hx.2)
    rcases hgv with ⟨y, ⟨u, hu, v, hv, rfl⟩, hy⟩
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [mul_assoc] using congrArg (fun z ↦ g₀⁻¹ * z) hy
  · apply inv_mul_notMem_mul_of_disjoint_leftCosets U₁ V g₁ gv
      (fun x hx ↦ hd1v x hx.1 hx.2)
    rcases hgv with ⟨y, ⟨u, hu, v, hv, rfl⟩, hy⟩
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [mul_assoc] using congrArg (fun z ↦ g₁⁻¹ * z) hy
  · apply inv_mul_notMem_mul_of_disjoint_leftCosets U₂ V g₂ gv
      (fun x hx ↦ hd2v x hx.1 hx.2)
    rcases hgv with ⟨y, ⟨u, hu, v, hv, rfl⟩, hy⟩
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [mul_assoc] using congrArg (fun z ↦ g₂⁻¹ * z) hy

private theorem p47_highIntersection_mul_low_eq_of_two
    {G : Type u} [Group G] [Finite G]
    (B X Y : Subgroup G) (r₂ rx ry : ℕ)
    (hB : B.index = 3 * r₂)
    (hX : X.index = 6 * rx) (hY : Y.index = 6 * ry)
    (hodd₂ : Odd r₂)
    (hc₂x : Nat.Coprime r₂ rx) (hc₂y : Nat.Coprime r₂ ry)
    (hBX : B.relIndex X = r₂)
    (hXY : X.relIndex Y = rx * 2) :
    (((X ⊓ Y : Subgroup G) : Set G) * (B : Set G)) =
      (X : Set G) * (B : Set G) := by
  let T : Subgroup G := X ⊓ Y
  have hTindex : T.index = 12 * (rx * ry) := by
    have h := Subgroup.relIndex_mul_index
      (H := X ⊓ Y) (K := Y) inf_le_right
    simp only [Subgroup.inf_relIndex_right] at h
    rw [hXY, hY] at h
    nlinarith
  have hBXne : B.relIndex X ≠ 0 := by
    rw [hBX]
    have hBne : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hB] at hBne
    omega
  have hupper : B.relIndex T ≤ r₂ := by
    simpa [T, hBX] using Subgroup.relIndex_le_of_le_right
      (H := B) (K := T) (L := X) inf_le_left hBXne
  have hinter : B.relIndex T * T.index = (B ⊓ T).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := B ⊓ T) (K := T) inf_le_right)
  have hraw : 3 * r₂ ∣ B.relIndex T * (12 * (rx * ry)) := by
    have hd := Subgroup.index_dvd_of_le (show B ⊓ T ≤ B from inf_le_left)
    rw [hB, ← hinter, hTindex] at hd
    exact hd
  have hcancel : r₂ ∣ B.relIndex T * (4 * (rx * ry)) := by
    have hraw' : 3 * r₂ ∣ 3 * (B.relIndex T * (4 * (rx * ry))) := by
      convert hraw using 1 <;> ring
    apply Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 3)
    exact hraw'
  have hcop4 : Nat.Coprime r₂ 4 := by
    simpa using hodd₂.coprime_two_right.pow_right 2
  have hcop : Nat.Coprime r₂ (4 * (rx * ry)) :=
    by simpa [mul_assoc] using (hcop4.mul_right hc₂x).mul_right hc₂y
  have hdvd : r₂ ∣ B.relIndex T := hcop.dvd_of_dvd_mul_right hcancel
  have hpositive : 0 < B.relIndex T := by
    have hne : B.relIndex T ≠ 0 := by
      intro hz
      exact hBXne (Subgroup.relIndex_eq_zero_of_le_right inf_le_left hz)
    exact Nat.pos_of_ne_zero hne
  have hrel : B.relIndex T = r₂ := by
    exact le_antisymm hupper (Nat.le_of_dvd hpositive hdvd)
  have hsubset : (T : Set G) * (B : Set G) ⊆
      (X : Set G) * (B : Set G) :=
    p47_product_subset_product_of_le_left T X B inf_le_left
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    natCard_subgroup_mul, natCard_subgroup_mul, hrel, hBX]

/-- Specialized source Claim 4 with the index-three anchor residual equal to
one.  A mixed `1/2` pair can only have high multiplier `1` or `3`, and the
residual at the multiplier-one high vertex is even. -/
private theorem p47_claim4_specialized
    {G : Type u} [Group G] [Finite G]
    (A B X Y : Subgroup G) (a b x y : G)
    (r₂ rx ry k : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hX : X.index = 6 * rx) (hY : Y.index = 6 * ry)
    (hodd₂ : Odd r₂)
    (hc₂x : Nat.Coprime r₂ rx) (hc₂y : Nat.Coprime r₂ ry)
    (hcxy : Nat.Coprime rx ry)
    (hkpos : 0 < k) (hklt : k < 6)
    (hAX : A.relIndex X = 1) (hXA : X.relIndex A = 2 * rx)
    (hBX : B.relIndex X = r₂) (hXB : X.relIndex B = 2 * rx)
    (hAY : A.relIndex Y = 2) (hYA : Y.relIndex A = 4 * ry)
    (hBY : B.relIndex Y = 2 * r₂)
    (hXY : X.relIndex Y = rx * k)
    (hdAB : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset b B t))
    (hdAX : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset x X t))
    (hdAY : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset y Y t))
    (hdBX : ∀ t, ¬(InLeftCoset b B t ∧ InLeftCoset x X t))
    (hdBY : ∀ t, ¬(InLeftCoset b B t ∧ InLeftCoset y Y t))
    (hdXY : ∀ t, ¬(InLeftCoset x X t ∧ InLeftCoset y Y t)) :
    (k = 1 ∨ k = 3) ∧ Even rx := by
  have hXle : X ≤ A := Subgroup.relIndex_eq_one.mp hAX
  have hXAset : (X : Set G) * (A : Set G) = A := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, hu, v, hv, rfl⟩
      exact A.mul_mem (hXle hu) hv
    · intro z hz
      exact ⟨1, X.one_mem, z, hz, one_mul z⟩
  have hXYsubsetAY : (X : Set G) * (Y : Set G) ⊆
      (A : Set G) * (Y : Set G) :=
    p47_product_subset_product_of_le_left X A Y hXle
  have hrypos : 0 < ry := by
    have hYne : Y.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hY] at hYne
    omega
  have hAYindex : (A ⊓ Y).index = 12 * ry := by
    have h := Subgroup.relIndex_mul_index
      (H := A ⊓ Y) (K := Y) inf_le_right
    simp only [Subgroup.inf_relIndex_right] at h
    rw [hAY, hY] at h
    omega
  have hXYindex : (X ⊓ Y).index = 6 * (rx * ry * k) := by
    have h := Subgroup.relIndex_mul_index
      (H := X ⊓ Y) (K := Y) inf_le_right
    simp only [Subgroup.inf_relIndex_right] at h
    rw [hXY, hY] at h
    nlinarith
  have hleInter : X ⊓ Y ≤ A ⊓ Y := by
    intro z hz
    exact ⟨hXle hz.1, hz.2⟩
  have hdivRaw : 12 * ry ∣ 6 * (rx * ry * k) := by
    rw [← hAYindex, ← hXYindex]
    exact Subgroup.index_dvd_of_le hleInter
  have htwo : 2 ∣ rx * k := by
    have hscaled : (6 * ry) * 2 ∣ (6 * ry) * (rx * k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdivRaw
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) hscaled
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨Or.inl rfl, even_iff_two_dvd.mpr (by simpa using htwo)⟩
  · have hTmul := p47_highIntersection_mul_low_eq_of_two B X Y
      r₂ rx ry hB hX hY hodd₂ hc₂x hc₂y hBX (by simpa using hXY)
    have hsub01 : (X : Set G) * (A : Set G) ⊆
        (B : Set G) * (A : Set G) := by
      rw [hXAset]
      intro z hz
      exact ⟨1, B.one_mem, z, hz, one_mul z⟩
    have hsub02 : (X : Set G) * (A : Set G) ⊆
        (Y : Set G) * (A : Set G) := by
      rw [hXAset]
      intro z hz
      exact ⟨1, Y.one_mem, z, hz, one_mul z⟩
    have hsub12 : (X : Set G) * (B : Set G) ⊆
        (Y : Set G) * (B : Set G) := by
      rw [← hTmul]
      exact p47_product_subset_product_of_le_left (X ⊓ Y) Y B inf_le_right
    have hX3 : X.index = 3 * (2 * rx) := by omega
    have hcardAX := p47_three_mul_productCard A X (r := 2 * rx) (k := 1)
      hX3 (by simpa using hXA)
    have hcardBX := p47_three_mul_productCard B X (r := 2 * rx) (k := 1)
      hX3 (by simpa using hXB)
    have hcardYX := p47_six_mul_productCard Y X (r := rx) (k := 2)
      hX (by simpa using hXY)
    have hcover : Nat.card G ≤
        Nat.card ((A : Set G) * (X : Set G)) +
        Nat.card ((B : Set G) * (X : Set G)) +
        Nat.card ((Y : Set G) * (X : Set G)) := by omega
    exact False.elim (p47_lemma35_three A B Y X a b y x
      (p47_harmonic4 A B Y X a b y x hdAB hdAY hdAX hdBY hdBX
        (fun z hz ↦ hdXY z ⟨hz.2, hz.1⟩))
      hsub01 hsub02 hsub12 hcover)
  · have hEven : Even rx := by
      exact even_iff_two_dvd.mpr
        ((by norm_num : Nat.Coprime 2 3).dvd_of_dvd_mul_right htwo)
    exact ⟨Or.inr rfl, hEven⟩
  · have hA3 : A.index = 3 * 1 := by simpa using hA
    have hX3 : X.index = 3 * (2 * rx) := by omega
    have hcardYX := p47_six_mul_productCard Y X (r := rx) (k := 4)
      hX (by simpa using hXY)
    have hcardAX := p47_three_mul_productCard A X (r := 2 * rx) (k := 1)
      hX3 (by simpa using hXA)
    have hcover : Nat.card G ≤
        Nat.card ((Y : Set G) * (X : Set G)) +
        Nat.card ((A : Set G) * (X : Set G)) := by omega
    exact False.elim (not_harmonic_three_of_product_cover Y A X y a x
      (fun z hz ↦ hdAY z ⟨hz.2, hz.1⟩)
      (fun z hz ↦ hdXY z ⟨hz.2, hz.1⟩) hdAX hXYsubsetAY hcover)
  · have hcardXY := p47_six_mul_productCard X Y (r := ry) (k := 5)
      hY (by
        have hrxpos : 0 < rx := by
          have hXne : X.index ≠ 0 := Subgroup.index_ne_zero_of_finite
          rw [hX] at hXne
          omega
        have hrev := p47_reverseRelIndex X Y (m := 6) (r := rx)
          (s := ry) (k := 5) hX hY hrxpos (by simpa using hXY)
        simpa [mul_comm] using hrev)
    have hY3 : Y.index = 3 * (2 * ry) := by omega
    have hcardAY := p47_three_mul_productCard A Y (r := 2 * ry) (k := 2)
      hY3 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hYA)
    have hcardLe : Nat.card ((X : Set G) * (Y : Set G)) ≤
        Nat.card ((A : Set G) * (Y : Set G)) := by
      have hn := Set.ncard_le_ncard hXYsubsetAY
      simpa only [Nat.card_coe_set_eq] using hn
    have hGpos : 0 < Nat.card G := Nat.card_pos
    omega

/-! ## Restricting chosen cells to one index-three box -/

private theorem p47_harmonicInsideAnchor
    {G : Type u} [Group G] {n : ℕ}
    (A : Subgroup G) (U : Fin n → Subgroup G) (g : Fin n → G)
    (base : G) (s : Fin n → A)
    (hpoint : ∀ i, InLeftCoset (g i) (U i) (base * (s i : G)))
    (hh : IsHarmonicCosetFamily g U) :
    IsHarmonicCosetFamily s (fun i ↦ (U i).subgroupOf A) := by
  intro i j hij y hy
  apply hh hij (base * (y : G))
  constructor
  · have hp := hpoint i
    have hi := hy.1
    change (g i)⁻¹ * (base * (s i : G)) ∈ U i at hp
    change (((s i)⁻¹ * y : A) : G) ∈ U i at hi
    have hmul := (U i).mul_mem hp hi
    simpa [InLeftCoset, mul_assoc] using hmul
  · have hp := hpoint j
    have hj := hy.2
    change (g j)⁻¹ * (base * (s j : G)) ∈ U j at hp
    change (((s j)⁻¹ * y : A) : G) ∈ U j at hj
    have hmul := (U j).mul_mem hp hj
    simpa [InLeftCoset, mul_assoc] using hmul

private theorem p47_exists_cell_point_in_other_anchor_box
    {G : Type u} [Group G] [Finite G]
    (A U : Subgroup G) (a u b : G)
    (hA : A.index = 3) (hrel : A.relIndex U = 2)
    (hdisjoint : ∀ z, ¬(InLeftCoset a A z ∧ InLeftCoset u U z))
    (hb : (QuotientGroup.mk b : G ⧸ A) ≠ QuotientGroup.mk a) :
    ∃ v : U, (QuotientGroup.mk (u * (v : G)) : G ⧸ A) =
      QuotientGroup.mk b := by
  classical
  have hAne : A.index ≠ 0 := by omega
  have hrelne : A.relIndex U ≠ 0 := by omega
  letI : Fintype (G ⧸ A) := A.fintypeOfIndexNeZero hAne
  letI : Fintype (U ⧸ A.subgroupOf U) :=
    (A.subgroupOf U).fintypeOfIndexNeZero hrelne
  let emb := shiftedCellBoxEmbedding A U u
  by_contra hnone
  have hmiss : ∀ q : U ⧸ A.subgroupOf U,
      emb q ≠ (QuotientGroup.mk b : G ⧸ A) := by
    intro q hq
    apply hnone
    induction q using QuotientGroup.induction_on with
    | _ v =>
        exact ⟨v, by simpa [emb] using hq⟩
  let F : Option (U ⧸ A.subgroupOf U) → G ⧸ A
    | none => QuotientGroup.mk b
    | some q => emb q
  have hFinj : Function.Injective F := by
    intro p q hpq
    cases p with
    | none =>
        cases q with
        | none => rfl
        | some q => exact False.elim (hmiss q hpq.symm)
    | some p =>
        cases q with
        | none => exact False.elim (hmiss p hpq)
        | some q =>
            congr
            exact emb.injective hpq
  have hdomCard : Fintype.card (U ⧸ A.subgroupOf U) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← (A.subgroupOf U).index_eq_card]
    exact hrel
  have hcard : Fintype.card (Option (U ⧸ A.subgroupOf U)) =
      Fintype.card (G ⧸ A) := by
    rw [Fintype.card_option, hdomCard, ← Nat.card_eq_fintype_card,
      ← A.index_eq_card, hA]
  have hsurj : Function.Surjective F :=
    ((Fintype.bijective_iff_injective_and_card F).2 ⟨hFinj, hcard⟩).2
  rcases hsurj (QuotientGroup.mk a) with ⟨q, hq⟩
  cases q with
  | none =>
      exact hb (by simpa [F] using hq)
  | some q =>
      induction q using QuotientGroup.induction_on with
      | _ v =>
          have hbox : (QuotientGroup.mk (u * (v : G)) : G ⧸ A) =
              QuotientGroup.mk a := by
            simpa [F, emb] using hq
          have hAcell : InLeftCoset a A (u * (v : G)) := by
            rw [InLeftCoset, ← QuotientGroup.eq]
            exact hbox.symm
          have hUcell : InLeftCoset u U (u * (v : G)) := by
            simpa [InLeftCoset] using v.property
          exact hdisjoint _ ⟨hAcell, hUcell⟩

private theorem p47_allTwo_impossible
    {G : Type u} [Group G] [Finite G]
    (A B C D E : Subgroup G) (a b c d e : G)
    (r₂ r₃ r₄ r₅ : ℕ)
    (hA : A.index = 3)
    (hBA : B.relIndex A = 2 * r₂)
    (hAC : A.relIndex C = 2) (hAD : A.relIndex D = 2)
    (hAE : A.relIndex E = 2)
    (hCA : C.relIndex A = 4 * r₃)
    (hDA : D.relIndex A = 4 * r₄)
    (hEA : E.relIndex A = 4 * r₅)
    (hodd₂ : Odd r₂)
    (hc₂₃ : Nat.Coprime r₂ r₃) (hc₂₄ : Nat.Coprime r₂ r₄)
    (hc₂₅ : Nat.Coprime r₂ r₅) (hc₃₄ : Nat.Coprime r₃ r₄)
    (hc₃₅ : Nat.Coprime r₃ r₅) (hc₄₅ : Nat.Coprime r₄ r₅)
    (hh : IsHarmonicCosetFamily ![a, b, c, d, e] ![A, B, C, D, E]) :
    False := by
  have hdAB := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hdAC := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdAD := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdAE := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdBC := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdBD := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdBE := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdCD := hh (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdCE := hh (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdDE := hh (i := (3 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hdAB hdAC hdAD hdAE hdBC hdBD hdBE hdCD hdCE hdDE
  have hbne : (QuotientGroup.mk b : G ⧸ A) ≠ QuotientGroup.mk a :=
    p47_quotient_ne_anchor_cell A B a b (fun z hz ↦ hdAB z hz.1 hz.2)
  rcases p47_exists_cell_point_in_other_anchor_box A C a c b hA hAC
      (fun z hz ↦ hdAC z hz.1 hz.2) hbne with ⟨vC, hvC⟩
  rcases p47_exists_cell_point_in_other_anchor_box A D a d b hA hAD
      (fun z hz ↦ hdAD z hz.1 hz.2) hbne with ⟨vD, hvD⟩
  rcases p47_exists_cell_point_in_other_anchor_box A E a e b hA hAE
      (fun z hz ↦ hdAE z hz.1 hz.2) hbne with ⟨vE, hvE⟩
  have hCmem : b⁻¹ * (c * (vC : G)) ∈ A := by
    rw [← QuotientGroup.eq]
    exact hvC.symm
  have hDmem : b⁻¹ * (d * (vD : G)) ∈ A := by
    rw [← QuotientGroup.eq]
    exact hvD.symm
  have hEmem : b⁻¹ * (e * (vE : G)) ∈ A := by
    rw [← QuotientGroup.eq]
    exact hvE.symm
  let sC : A := ⟨b⁻¹ * (c * (vC : G)), hCmem⟩
  let sD : A := ⟨b⁻¹ * (d * (vD : G)), hDmem⟩
  let sE : A := ⟨b⁻¹ * (e * (vE : G)), hEmem⟩
  let g₄ : Fin 4 → G := ![b, c, d, e]
  let U₄ : Fin 4 → Subgroup G := ![B, C, D, E]
  let s₄ : Fin 4 → A := ![1, sC, sD, sE]
  let r₄v : Fin 4 → ℕ := ![r₂, r₃, r₄, r₅]
  have hpoint : ∀ i, InLeftCoset (g₄ i) (U₄ i) (b * (s₄ i : G)) := by
    intro i
    fin_cases i
    · simp [g₄, U₄, s₄, InLeftCoset]
    · simpa [g₄, U₄, s₄, sC, InLeftCoset, mul_assoc] using vC.property
    · simpa [g₄, U₄, s₄, sD, InLeftCoset, mul_assoc] using vD.property
    · simpa [g₄, U₄, s₄, sE, InLeftCoset, mul_assoc] using vE.property
  have hh₄ : IsHarmonicCosetFamily g₄ U₄ := by
    simpa [g₄, U₄] using p47_harmonic4 B C D E b c d e
      (fun z hz ↦ hdBC z hz.1 hz.2)
      (fun z hz ↦ hdBD z hz.1 hz.2)
      (fun z hz ↦ hdBE z hz.1 hz.2)
      (fun z hz ↦ hdCD z hz.1 hz.2)
      (fun z hz ↦ hdCE z hz.1 hz.2)
      (fun z hz ↦ hdDE z hz.1 hz.2)
  have hhA : IsHarmonicCosetFamily s₄ (fun i ↦ (U₄ i).subgroupOf A) :=
    p47_harmonicInsideAnchor A U₄ g₄ b s₄ hpoint hh₄
  apply margolisSchnabel_prop4_5_finite s₄
    (fun i ↦ (U₄ i).subgroupOf A) r₄v
  · change B.relIndex A = 2 * r₂
    exact hBA
  · intro i hi
    fin_cases i <;> simp_all [U₄, r₄v]
    · change C.relIndex A = 4 * r₃
      exact hCA
    · change D.relIndex A = 4 * r₄
      exact hDA
    · change E.relIndex A = 4 * r₅
      exact hEA
  · simpa [r₄v, Nat.odd_iff] using hodd₂
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [r₄v] at hij ⊢
    · exact hc₂₃
    · exact hc₂₄
    · exact hc₂₅
    · exact hc₂₃.symm
    · exact hc₃₄
    · exact hc₃₅
    · exact hc₂₄.symm
    · exact hc₃₄.symm
    · exact hc₄₅
    · exact hc₂₅.symm
    · exact hc₃₅.symm
    · exact hc₄₅.symm
  · exact hhA

private theorem p47_inLeftCoset_mul_right_member
    {G : Type u} [Group G] (U : Subgroup G) (g x : G) (v : U) :
    InLeftCoset (g * (v : G)) U x ↔ InLeftCoset g U x := by
  constructor
  · intro h
    change ((g * (v : G))⁻¹ * x) ∈ U at h
    change g⁻¹ * x ∈ U
    have := U.mul_mem v.property h
    simpa [mul_assoc] using this
  · intro h
    change g⁻¹ * x ∈ U at h
    change ((g * (v : G))⁻¹ * x) ∈ U
    simpa [mul_assoc] using U.mul_mem (U.inv_mem v.property) h

private theorem p47_mobileP42_impossible
    {G : Type u} [Group G] [Finite G]
    (A X Y Z : Subgroup G) (a x y z : G) (rx ry rz : ℕ)
    (hA : A.index = 3)
    (hAX : A.relIndex X = 2)
    (hXrel : X.relIndex A = 2 * rx)
    (hYrel : Y.relIndex A = 2 * ry)
    (hZrel : Z.relIndex A = 2 * rz)
    (hyzQ : (QuotientGroup.mk y : G ⧸ A) = QuotientGroup.mk z)
    (hdAX : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset x X t))
    (hdAY : ∀ t, ¬(InLeftCoset a A t ∧ InLeftCoset y Y t))
    (hdXY : ∀ t, ¬(InLeftCoset x X t ∧ InLeftCoset y Y t))
    (hdXZ : ∀ t, ¬(InLeftCoset x X t ∧ InLeftCoset z Z t))
    (hdYZ : ∀ t, ¬(InLeftCoset y Y t ∧ InLeftCoset z Z t))
    (hcxy : Nat.Coprime rx ry) (hcxz : Nat.Coprime rx rz)
    (hcyz : Nat.Coprime ry rz) : False := by
  have hyne : (QuotientGroup.mk y : G ⧸ A) ≠ QuotientGroup.mk a :=
    p47_quotient_ne_anchor_cell A Y a y hdAY
  rcases p47_exists_cell_point_in_other_anchor_box A X a x y hA hAX hdAX hyne with
    ⟨v, hv⟩
  let xv : G := x * (v : G)
  have hdXvY : ∀ t, ¬(InLeftCoset xv X t ∧ InLeftCoset y Y t) := by
    intro t ht
    exact hdXY t ⟨(p47_inLeftCoset_mul_right_member X x t v).mp ht.1, ht.2⟩
  have hdXvZ : ∀ t, ¬(InLeftCoset xv X t ∧ InLeftCoset z Z t) := by
    intro t ht
    exact hdXZ t ⟨(p47_inLeftCoset_mul_right_member X x t v).mp ht.1, ht.2⟩
  exact p47_p42_inside_anchor A X Y Z xv y z rx ry rz
    hXrel hYrel hZrel hv (hv.trans hyzQ)
    hdXvY hdXvZ hdYZ hcxy hcxz hcyz

private theorem p47_allOne_impossible
    {G : Type u} [Group G] [Finite G]
    (A B C D E : Subgroup G) (a b c d e : G)
    (r₂ r₃ r₄ r₅ : ℕ)
    (hA : A.index = 3) (hAB : A.relIndex B = 2)
    (hBA : B.relIndex A = 2 * r₂)
    (hCA : C.relIndex A = 2 * r₃)
    (hDA : D.relIndex A = 2 * r₄)
    (hEA : E.relIndex A = 2 * r₅)
    (hc₂₃ : Nat.Coprime r₂ r₃) (hc₂₄ : Nat.Coprime r₂ r₄)
    (hc₂₅ : Nat.Coprime r₂ r₅) (hc₃₄ : Nat.Coprime r₃ r₄)
    (hc₃₅ : Nat.Coprime r₃ r₅) (hc₄₅ : Nat.Coprime r₄ r₅)
    (hh : IsHarmonicCosetFamily ![a, b, c, d, e] ![A, B, C, D, E]) :
    False := by
  have hdAB := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hdAC := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdAD := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdAE := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdBC := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdBD := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdBE := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdCD := hh (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdCE := hh (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdDE := hh (i := (3 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hdAB hdAC hdAD hdAE hdBC hdBD hdBE hdCD hdCE hdDE
  let qa : G ⧸ A := QuotientGroup.mk a
  let qc : G ⧸ A := QuotientGroup.mk c
  let qd : G ⧸ A := QuotientGroup.mk d
  let qe : G ⧸ A := QuotientGroup.mk e
  have hca : qc ≠ qa := p47_quotient_ne_anchor_cell A C a c
    (fun z hz ↦ hdAC z hz.1 hz.2)
  have hda : qd ≠ qa := p47_quotient_ne_anchor_cell A D a d
    (fun z hz ↦ hdAD z hz.1 hz.2)
  have hea : qe ≠ qa := p47_quotient_ne_anchor_cell A E a e
    (fun z hz ↦ hdAE z hz.1 hz.2)
  have hpairs : qc = qd ∨ qc = qe ∨ qd = qe := by
    by_cases hcd : qc = qd
    · exact Or.inl hcd
    by_cases hce : qc = qe
    · exact Or.inr (Or.inl hce)
    exact Or.inr (Or.inr (p47_quotient_eq_of_avoids_two A hA qa qc qd qe
      hca.symm hda (fun h ↦ hcd h.symm) hea (fun h ↦ hce h.symm)))
  rcases hpairs with hcd | hce | hde
  · exact p47_mobileP42_impossible A B C D a b c d r₂ r₃ r₄
      hA hAB hBA hCA hDA hcd
      (fun z hz ↦ hdAB z hz.1 hz.2)
      (fun z hz ↦ hdAC z hz.1 hz.2)
      (fun z hz ↦ hdBC z hz.1 hz.2)
      (fun z hz ↦ hdBD z hz.1 hz.2)
      (fun z hz ↦ hdCD z hz.1 hz.2) hc₂₃ hc₂₄ hc₃₄
  · exact p47_mobileP42_impossible A B C E a b c e r₂ r₃ r₅
      hA hAB hBA hCA hEA hce
      (fun z hz ↦ hdAB z hz.1 hz.2)
      (fun z hz ↦ hdAC z hz.1 hz.2)
      (fun z hz ↦ hdBC z hz.1 hz.2)
      (fun z hz ↦ hdBE z hz.1 hz.2)
      (fun z hz ↦ hdCE z hz.1 hz.2) hc₂₃ hc₂₅ hc₃₅
  · exact p47_mobileP42_impossible A B D E a b d e r₂ r₄ r₅
      hA hAB hBA hDA hEA hde
      (fun z hz ↦ hdAB z hz.1 hz.2)
      (fun z hz ↦ hdAD z hz.1 hz.2)
      (fun z hz ↦ hdBD z hz.1 hz.2)
      (fun z hz ↦ hdBE z hz.1 hz.2)
      (fun z hz ↦ hdDE z hz.1 hz.2) hc₂₄ hc₂₅ hc₄₅

/-! ## The remaining mixed configuration -/

private theorem p47_alphaOneIntersection_mul_eq_high
    {G : Type u} [Group G] [Finite G]
    (Uj V Ui : Subgroup G) {rj rv ri : ℕ}
    (hUj : Uj.index = 6 * rj) (hV : V.index = 6 * rv)
    (hUi : Ui.index = 6 * ri)
    (hij : Nat.Coprime ri rj) (hiv : Nat.Coprime ri rv)
    (hrelUjV : Uj.relIndex V = rj)
    (hrelUiV : Ui.relIndex V = ri) :
    (((Uj ⊓ V : Subgroup G) : Set G) * (Ui : Set G)) =
      (V : Set G) * (Ui : Set G) := by
  let T : Subgroup G := Uj ⊓ V
  have hTindex : T.index = 6 * (rj * rv) := by
    calc
      T.index = Uj.relIndex V * V.index := by
        simpa [T, Subgroup.inf_relIndex_right] using
          (Subgroup.relIndex_mul_index (H := Uj ⊓ V) (K := V)
            inf_le_right).symm
      _ = rj * (6 * rv) := by rw [hrelUjV, hV]
      _ = 6 * (rj * rv) := by ring
  have hrelne : Ui.relIndex V ≠ 0 := by
    rw [hrelUiV]
    intro hri
    have hUifinite : Ui.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact hUifinite (by simp [hUi, hri])
  have hupper : Ui.relIndex T ≤ ri := by
    simpa [hrelUiV] using Subgroup.relIndex_le_of_le_right
      (H := Ui) (K := T) (L := V) inf_le_right hrelne
  have hdivIndex : Ui.index ∣ (Ui ⊓ T).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : Ui.relIndex T * T.index = (Ui ⊓ T).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := Ui ⊓ T) (K := T) inf_le_right)
  have hraw : 6 * ri ∣ Ui.relIndex T * (6 * (rj * rv)) := by
    rw [← hinter, hUi, hTindex] at hdivIndex
    exact hdivIndex
  have hcancel : ri ∣ Ui.relIndex T * (rj * rv) := by
    apply Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 6)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
  have hdiv : ri ∣ Ui.relIndex T :=
    (hij.mul_right hiv).dvd_of_dvd_mul_right hcancel
  have hpositive : 0 < Ui.relIndex T := by
    have hne : Ui.relIndex T ≠ 0 := by
      intro hz
      exact hrelne (Subgroup.relIndex_eq_zero_of_le_right inf_le_right hz)
    exact Nat.pos_of_ne_zero hne
  have hrel : Ui.relIndex T = ri := by
    rcases hdiv with ⟨k, hk⟩
    have hripos : 0 < ri := by
      by_contra h
      have : ri = 0 := Nat.eq_zero_of_not_pos h
      exact hrelne (by simp [hrelUiV, this])
    have hkpos : 0 < k := by
      by_contra h
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos h
      rw [hk, hkzero] at hpositive
      simp at hpositive
    have hkle : k ≤ 1 := by
      apply Nat.le_of_mul_le_mul_left (c := ri) (by simpa [hk] using hupper) hripos
    have : k = 1 := by omega
    simpa [this] using hk
  have hsubset : (T : Set G) * (Ui : Set G) ⊆
      (V : Set G) * (Ui : Set G) :=
    p47_product_subset_product_of_le_left T V Ui inf_le_right
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    natCard_subgroup_mul, natCard_subgroup_mul, hrel, hrelUiV]

private theorem p47_alphaOneIntersection_mul_eq_low
    {G : Type u} [Group G] [Finite G]
    (Uj V Ui : Subgroup G) {rj rv ri : ℕ}
    (hUj : Uj.index = 6 * rj) (hV : V.index = 6 * rv)
    (hUi : Ui.index = 3 * ri) (hodd : Odd ri)
    (hij : Nat.Coprime ri rj) (hiv : Nat.Coprime ri rv)
    (hrelUjV : Uj.relIndex V = rj)
    (hrelUiV : Ui.relIndex V = ri) :
    (((Uj ⊓ V : Subgroup G) : Set G) * (Ui : Set G)) =
      (V : Set G) * (Ui : Set G) := by
  let T : Subgroup G := Uj ⊓ V
  have hTindex : T.index = 6 * (rj * rv) := by
    calc
      T.index = Uj.relIndex V * V.index := by
        simpa [T, Subgroup.inf_relIndex_right] using
          (Subgroup.relIndex_mul_index (H := Uj ⊓ V) (K := V)
            inf_le_right).symm
      _ = rj * (6 * rv) := by rw [hrelUjV, hV]
      _ = 6 * (rj * rv) := by ring
  have hrelne : Ui.relIndex V ≠ 0 := by
    rw [hrelUiV]
    intro hri
    have hUifinite : Ui.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact hUifinite (by simp [hUi, hri])
  have hupper : Ui.relIndex T ≤ ri := by
    simpa [hrelUiV] using Subgroup.relIndex_le_of_le_right
      (H := Ui) (K := T) (L := V) inf_le_right hrelne
  have hdivIndex : Ui.index ∣ (Ui ⊓ T).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : Ui.relIndex T * T.index = (Ui ⊓ T).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := Ui ⊓ T) (K := T) inf_le_right)
  have hraw : 3 * ri ∣ Ui.relIndex T * (6 * (rj * rv)) := by
    rw [← hinter, hUi, hTindex] at hdivIndex
    exact hdivIndex
  have hcancel : ri ∣ Ui.relIndex T * (2 * (rj * rv)) := by
    have hraw' : 3 * ri ∣ 3 * (Ui.relIndex T * (2 * (rj * rv))) := by
      convert hraw using 1 <;> ring
    exact Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 3) hraw'
  have hcop : Nat.Coprime ri (2 * (rj * rv)) :=
    hodd.coprime_two_right.mul_right (hij.mul_right hiv)
  have hdiv : ri ∣ Ui.relIndex T := hcop.dvd_of_dvd_mul_right hcancel
  have hpositive : 0 < Ui.relIndex T := by
    have hne : Ui.relIndex T ≠ 0 := by
      intro hz
      exact hrelne (Subgroup.relIndex_eq_zero_of_le_right inf_le_right hz)
    exact Nat.pos_of_ne_zero hne
  have hrel : Ui.relIndex T = ri := by
    rcases hdiv with ⟨k, hk⟩
    have hripos : 0 < ri := by
      by_contra h
      have : ri = 0 := Nat.eq_zero_of_not_pos h
      exact hrelne (by simp [hrelUiV, this])
    have hkpos : 0 < k := by
      by_contra h
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos h
      rw [hk, hkzero] at hpositive
      simp at hpositive
    have hkle : k ≤ 1 := by
      apply Nat.le_of_mul_le_mul_left (c := ri) (by simpa [hk] using hupper) hripos
    have : k = 1 := by omega
    simpa [this] using hk
  have hsubset : (T : Set G) * (Ui : Set G) ⊆
      (V : Set G) * (Ui : Set G) :=
    p47_product_subset_product_of_le_left T V Ui inf_le_right
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    natCard_subgroup_mul, natCard_subgroup_mul, hrel, hrelUiV]

private theorem p47_harmonic_reindex
    {G : Type u} [Group G] {m n : ℕ}
    (g : Fin n → G) (U : Fin n → Subgroup G)
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (hh : IsHarmonicCosetFamily g U) :
    IsHarmonicCosetFamily (g ∘ f) (U ∘ f) := by
  intro i j hij
  exact hh (fun h ↦ hij (hf h))

private theorem p47_anchor_not_mem_thickened
    {G : Type u} [Group G]
    (U V : Subgroup G) (g gv : G)
    (hdisjoint : ∀ x, ¬(InLeftCoset g U x ∧ InLeftCoset gv V x)) :
    gv ∉ g • ((U : Set G) * (V : Set G)) := by
  intro hgv
  apply inv_mul_notMem_mul_of_disjoint_leftCosets U V g gv hdisjoint
  rcases hgv with ⟨y, ⟨u, hu, v, hv, rfl⟩, hy⟩
  refine ⟨u, hu, v, hv, ?_⟩
  simpa [mul_assoc] using congrArg (fun z ↦ g⁻¹ * z) hy

private theorem p47_lemma35_four
    {G : Type u} [Group G] [Finite G]
    (U₀ U₁ U₂ U₃ V : Subgroup G) (g₀ g₁ g₂ g₃ gv : G)
    (hh : IsHarmonicCosetFamily ![g₀, g₁, g₂, g₃, gv]
      ![U₀, U₁, U₂, U₃, V])
    (hsub01 : (V : Set G) * (U₀ : Set G) ⊆
      (U₁ : Set G) * (U₀ : Set G))
    (hsub02 : (V : Set G) * (U₀ : Set G) ⊆
      (U₂ : Set G) * (U₀ : Set G))
    (hsub03 : (V : Set G) * (U₀ : Set G) ⊆
      (U₃ : Set G) * (U₀ : Set G))
    (hsub12 : (V : Set G) * (U₁ : Set G) ⊆
      (U₂ : Set G) * (U₁ : Set G))
    (hsub13 : (V : Set G) * (U₁ : Set G) ⊆
      (U₃ : Set G) * (U₁ : Set G))
    (hsub23 : (V : Set G) * (U₂ : Set G) ⊆
      (U₃ : Set G) * (U₂ : Set G))
    (hcover : Nat.card G ≤
      Nat.card ((U₀ : Set G) * (V : Set G)) +
      Nat.card ((U₁ : Set G) * (V : Set G)) +
      Nat.card ((U₂ : Set G) * (V : Set G)) +
      Nat.card ((U₃ : Set G) * (V : Set G))) : False := by
  classical
  have hd01 := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hd02 := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hd03 := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hd0v := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hd12 := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hd13 := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hd1v := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hd23 := hh (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hd2v := hh (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hd3v := hh (i := (3 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hd01 hd02 hd03 hd0v hd12 hd13 hd1v hd23 hd2v hd3v
  let S₀ : Set G := g₀ • ((U₀ : Set G) * (V : Set G))
  let S₁ : Set G := g₁ • ((U₁ : Set G) * (V : Set G))
  let S₂ : Set G := g₂ • ((U₂ : Set G) * (V : Set G))
  let S₃ : Set G := g₃ • ((U₃ : Set G) * (V : Set G))
  have hdS01 : Disjoint S₀ S₁ := p47_thickenedDisjoint U₀ U₁ V g₀ g₁ gv
    (fun x hx ↦ hd01 x hx.1 hx.2) (fun x hx ↦ hd0v x hx.1 hx.2)
    (fun x hx ↦ hd1v x hx.1 hx.2) hsub01
  have hdS02 : Disjoint S₀ S₂ := p47_thickenedDisjoint U₀ U₂ V g₀ g₂ gv
    (fun x hx ↦ hd02 x hx.1 hx.2) (fun x hx ↦ hd0v x hx.1 hx.2)
    (fun x hx ↦ hd2v x hx.1 hx.2) hsub02
  have hdS03 : Disjoint S₀ S₃ := p47_thickenedDisjoint U₀ U₃ V g₀ g₃ gv
    (fun x hx ↦ hd03 x hx.1 hx.2) (fun x hx ↦ hd0v x hx.1 hx.2)
    (fun x hx ↦ hd3v x hx.1 hx.2) hsub03
  have hdS12 : Disjoint S₁ S₂ := p47_thickenedDisjoint U₁ U₂ V g₁ g₂ gv
    (fun x hx ↦ hd12 x hx.1 hx.2) (fun x hx ↦ hd1v x hx.1 hx.2)
    (fun x hx ↦ hd2v x hx.1 hx.2) hsub12
  have hdS13 : Disjoint S₁ S₃ := p47_thickenedDisjoint U₁ U₃ V g₁ g₃ gv
    (fun x hx ↦ hd13 x hx.1 hx.2) (fun x hx ↦ hd1v x hx.1 hx.2)
    (fun x hx ↦ hd3v x hx.1 hx.2) hsub13
  have hdS23 : Disjoint S₂ S₃ := p47_thickenedDisjoint U₂ U₃ V g₂ g₃ gv
    (fun x hx ↦ hd23 x hx.1 hx.2) (fun x hx ↦ hd2v x hx.1 hx.2)
    (fun x hx ↦ hd3v x hx.1 hx.2) hsub23
  have hd01_2 : Disjoint (S₀ ∪ S₁) S₂ :=
    Set.disjoint_union_left.2 ⟨hdS02, hdS12⟩
  have hd01_3 : Disjoint (S₀ ∪ S₁) S₃ :=
    Set.disjoint_union_left.2 ⟨hdS03, hdS13⟩
  have hd012_3 : Disjoint ((S₀ ∪ S₁) ∪ S₂) S₃ :=
    Set.disjoint_union_left.2 ⟨hd01_3, hdS23⟩
  have hcardLower : Nat.card G ≤ (((S₀ ∪ S₁) ∪ S₂) ∪ S₃).ncard := by
    rw [Set.ncard_union_eq hd012_3, Set.ncard_union_eq hd01_2,
      Set.ncard_union_eq hdS01]
    simp only [S₀, S₁, S₂, S₃, Set.ncard_smul_set]
    simpa only [Nat.card_coe_set_eq] using hcover
  have hfull : ((S₀ ∪ S₁) ∪ S₂) ∪ S₃ = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by simpa using hcardLower)
  have hgv : gv ∈ ((S₀ ∪ S₁) ∪ S₂) ∪ S₃ := by rw [hfull]; trivial
  rcases hgv with ((hgv | hgv) | hgv) | hgv
  · exact p47_anchor_not_mem_thickened U₀ V g₀ gv
      (fun x hx ↦ hd0v x hx.1 hx.2) hgv
  · exact p47_anchor_not_mem_thickened U₁ V g₁ gv
      (fun x hx ↦ hd1v x hx.1 hx.2) hgv
  · exact p47_anchor_not_mem_thickened U₂ V g₂ gv
      (fun x hx ↦ hd2v x hx.1 hx.2) hgv
  · exact p47_anchor_not_mem_thickened U₃ V g₃ gv
      (fun x hx ↦ hd3v x hx.1 hx.2) hgv

private theorem p47_mixedOnes_impossible
    {G : Type u} [Group G] [Finite G]
    (A B X Y Z : Subgroup G) (a b x y z : G)
    (r₂ rx ry rz : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hX : X.index = 6 * rx) (hY : Y.index = 6 * ry)
    (hZ : Z.index = 6 * rz)
    (hodd₂ : Odd r₂)
    (hc₂x : Nat.Coprime r₂ rx) (hc₂y : Nat.Coprime r₂ ry)
    (hc₂z : Nat.Coprime r₂ rz) (hcxy : Nat.Coprime rx ry)
    (hcxz : Nat.Coprime rx rz) (hcyz : Nat.Coprime ry rz)
    (hAX : A.relIndex X = 1) (hXA : X.relIndex A = 2 * rx)
    (hBX : B.relIndex X = r₂) (hXB : X.relIndex B = 2 * rx)
    (hXY : X.relIndex Y = rx) (hYX : Y.relIndex X = ry)
    (hXZ : X.relIndex Z = rx) (hZX : Z.relIndex X = rz)
    (hh : IsHarmonicCosetFamily ![a, b, x, y, z] ![A, B, X, Y, Z]) :
    False := by
  have hXle : X ≤ A := Subgroup.relIndex_eq_one.mp hAX
  have hXAset : (X : Set G) * (A : Set G) = A := by
    apply Set.Subset.antisymm
    · rintro t ⟨u, hu, v, hv, rfl⟩
      exact A.mul_mem (hXle hu) hv
    · intro t ht
      exact ⟨1, X.one_mem, t, ht, one_mul t⟩
  have heqYA := p47_alphaOneIntersection_mul_eq_low
    (rj := ry) (rv := rx) (ri := 1) Y X A
    hY hX (by omega) (by simp) (by simp) (by simp) hYX hAX
  have heqZA := p47_alphaOneIntersection_mul_eq_low
    (rj := rz) (rv := rx) (ri := 1) Z X A
    hZ hX (by omega) (by simp) (by simp) (by simp) hZX hAX
  have heqYB := p47_alphaOneIntersection_mul_eq_low Y X B
    hY hX hB hodd₂ hc₂y hc₂x hYX hBX
  have heqZB := p47_alphaOneIntersection_mul_eq_low Z X B
    hZ hX hB hodd₂ hc₂z hc₂x hZX hBX
  have heqZY := p47_alphaOneIntersection_mul_eq_high Z X Y
    hZ hX hY hcyz hcxy.symm hZX hYX
  have hsubAY : (X : Set G) * (A : Set G) ⊆
      (Y : Set G) * (A : Set G) := by
    rw [← heqYA]
    exact p47_product_subset_product_of_le_left (Y ⊓ X) Y A inf_le_left
  have hsubAZ : (X : Set G) * (A : Set G) ⊆
      (Z : Set G) * (A : Set G) := by
    rw [← heqZA]
    exact p47_product_subset_product_of_le_left (Z ⊓ X) Z A inf_le_left
  have hsubBY : (X : Set G) * (B : Set G) ⊆
      (Y : Set G) * (B : Set G) := by
    rw [← heqYB]
    exact p47_product_subset_product_of_le_left (Y ⊓ X) Y B inf_le_left
  have hsubBZ : (X : Set G) * (B : Set G) ⊆
      (Z : Set G) * (B : Set G) := by
    rw [← heqZB]
    exact p47_product_subset_product_of_le_left (Z ⊓ X) Z B inf_le_left
  have hsubYZ : (X : Set G) * (Y : Set G) ⊆
      (Z : Set G) * (Y : Set G) := by
    rw [← heqZY]
    exact p47_product_subset_product_of_le_left (Z ⊓ X) Z Y inf_le_left
  have hsubAB : (X : Set G) * (A : Set G) ⊆
      (B : Set G) * (A : Set G) := by
    rw [hXAset]
    intro t ht
    exact ⟨1, B.one_mem, t, ht, one_mul t⟩
  let f : Fin 5 → Fin 5 := ![0, 1, 3, 4, 2]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
  have hh' : IsHarmonicCosetFamily ![a, b, y, z, x] ![A, B, Y, Z, X] := by
    convert p47_harmonic_reindex ![a, b, x, y, z] ![A, B, X, Y, Z] f hf hh
      using 1 <;> funext i <;> fin_cases i <;> rfl
  have hcardAX := p47_six_mul_productCard A X (r := rx) (k := 2) hX
    (by simpa [mul_comm] using hXA)
  have hcardBX := p47_six_mul_productCard B X (r := rx) (k := 2) hX
    (by simpa [mul_comm] using hXB)
  have hcardYX := p47_six_mul_productCard Y X (r := rx) (k := 1) hX
    (by simpa using hXY)
  have hcardZX := p47_six_mul_productCard Z X (r := rx) (k := 1) hX
    (by simpa using hXZ)
  have hcover : Nat.card G ≤
      Nat.card ((A : Set G) * (X : Set G)) +
      Nat.card ((B : Set G) * (X : Set G)) +
      Nat.card ((Y : Set G) * (X : Set G)) +
      Nat.card ((Z : Set G) * (X : Set G)) := by omega
  exact p47_lemma35_four A B Y Z X a b y z x hh'
    hsubAB hsubAY hsubAZ hsubBY hsubBZ hsubYZ hcover

private theorem p47_mixedThree_impossible
    {G : Type u} [Group G] [Finite G]
    (A B X Y : Subgroup G) (r₂ rx ry : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hY : Y.index = 6 * ry)
    (hodd₂ : Odd r₂)
    (hAB : A.relIndex B = 2) (hBA : B.relIndex A = 2 * r₂)
    (hAX : A.relIndex X = 1)
    (hAY : A.relIndex Y = 2)
    (hBX : B.relIndex X = r₂)
    (hYX : Y.relIndex X = ry * 3) : False := by
  have hABCard := p47_three_mul_productCard A B (r := r₂) (k := 2)
    hB (by simpa [mul_comm] using hBA)
  have hXle : X ≤ A := Subgroup.relIndex_eq_one.mp hAX
  have hAXset : (A : Set G) * (X : Set G) = A := by
    apply Set.Subset.antisymm
    · rintro t ⟨u, hu, v, hv, rfl⟩
      exact A.mul_mem hu (hXle hv)
    · intro t ht
      exact ⟨t, ht, 1, X.one_mem, mul_one t⟩
  have hACard : Nat.card ((A : Set G) * (X : Set G)) = Nat.card A := by
    rw [hAXset]
    rfl
  have hXYCard := p47_six_mul_productCard X Y (r := ry) (k := 3) hY hYX
  have hCDCard : 2 * Nat.card ((X : Set G) * (Y : Set G)) = Nat.card G := by
    omega
  exact indexThreeAction_configuration_impossible A B X Y r₂
    hA hAB hAY hABCard hACard hCDCard hBX hodd₂

private theorem p47_coprime_not_both_even {r s : ℕ}
    (hcop : Nat.Coprime r s) (hr : Even r) (hs : Even s) : False := by
  have htwo : 2 ∣ Nat.gcd r s := Nat.dvd_gcd hr.two_dvd hs.two_dvd
  rw [hcop.gcd_eq_one] at htwo
  norm_num at htwo

private theorem p47_twoOneOne_impossible
    {G : Type u} [Group G] [Finite G]
    (A B X Z Y : Subgroup G) (a b x z y : G)
    (r₂ rx rz ry kXY kZY : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hX : X.index = 6 * rx) (hZ : Z.index = 6 * rz)
    (hY : Y.index = 6 * ry)
    (hodd₂ : Odd r₂)
    (hc₂x : Nat.Coprime r₂ rx) (hc₂z : Nat.Coprime r₂ rz)
    (hc₂y : Nat.Coprime r₂ ry) (hcxz : Nat.Coprime rx rz)
    (hcxy : Nat.Coprime rx ry) (hczy : Nat.Coprime rz ry)
    (hkXYpos : 0 < kXY) (hkXYlt : kXY < 6)
    (hkZYpos : 0 < kZY) (hkZYlt : kZY < 6)
    (hAX : A.relIndex X = 1) (hXA : X.relIndex A = 2 * rx)
    (hBX : B.relIndex X = r₂) (hXB : X.relIndex B = 2 * rx)
    (hAZ : A.relIndex Z = 1) (hZA : Z.relIndex A = 2 * rz)
    (hBZ : B.relIndex Z = r₂) (hZB : Z.relIndex B = 2 * rz)
    (hAY : A.relIndex Y = 2) (hYA : Y.relIndex A = 4 * ry)
    (hBY : B.relIndex Y = 2 * r₂)
    (hXY : X.relIndex Y = rx * kXY)
    (hZY : Z.relIndex Y = rz * kZY)
    (hh : IsHarmonicCosetFamily ![a, b, x, z, y] ![A, B, X, Z, Y]) : False := by
  have hdAB := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hdAX := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdAZ := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdAY := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdBX := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdBZ := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdBY := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdXY := hh (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdZY := hh (i := (3 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hdAB hdAX hdAZ hdAY hdBX hdBZ hdBY hdXY hdZY
  have hxEven := (p47_claim4_specialized A B X Y a b x y
    r₂ rx ry kXY hA hB hX hY hodd₂ hc₂x hc₂y hcxy
    hkXYpos hkXYlt hAX hXA hBX hXB hAY hYA hBY hXY
    (fun t ht ↦ hdAB t ht.1 ht.2) (fun t ht ↦ hdAX t ht.1 ht.2)
    (fun t ht ↦ hdAY t ht.1 ht.2) (fun t ht ↦ hdBX t ht.1 ht.2)
    (fun t ht ↦ hdBY t ht.1 ht.2) (fun t ht ↦ hdXY t ht.1 ht.2)).2
  have hzEven := (p47_claim4_specialized A B Z Y a b z y
    r₂ rz ry kZY hA hB hZ hY hodd₂ hc₂z hc₂y hczy
    hkZYpos hkZYlt hAZ hZA hBZ hZB hAY hYA hBY hZY
    (fun t ht ↦ hdAB t ht.1 ht.2) (fun t ht ↦ hdAZ t ht.1 ht.2)
    (fun t ht ↦ hdAY t ht.1 ht.2) (fun t ht ↦ hdBZ t ht.1 ht.2)
    (fun t ht ↦ hdBY t ht.1 ht.2) (fun t ht ↦ hdZY t ht.1 ht.2)).2
  exact p47_coprime_not_both_even hcxz hxEven hzEven

private theorem p47_oneTwoTwo_impossible
    {G : Type u} [Group G] [Finite G]
    (A B X Y Z : Subgroup G) (a b x y z : G)
    (r₂ rx ry rz kXY kXZ : ℕ)
    (hA : A.index = 3) (hB : B.index = 3 * r₂)
    (hX : X.index = 6 * rx) (hY : Y.index = 6 * ry)
    (hZ : Z.index = 6 * rz)
    (hodd₂ : Odd r₂)
    (hc₂x : Nat.Coprime r₂ rx) (hc₂y : Nat.Coprime r₂ ry)
    (hc₂z : Nat.Coprime r₂ rz) (hcxy : Nat.Coprime rx ry)
    (hcxz : Nat.Coprime rx rz) (hcyz : Nat.Coprime ry rz)
    (hkXYpos : 0 < kXY) (hkXYlt : kXY < 6)
    (hkXZpos : 0 < kXZ) (hkXZlt : kXZ < 6)
    (hAB : A.relIndex B = 2) (hBA : B.relIndex A = 2 * r₂)
    (hAX : A.relIndex X = 1) (hXA : X.relIndex A = 2 * rx)
    (hBX : B.relIndex X = r₂) (hXB : X.relIndex B = 2 * rx)
    (hAY : A.relIndex Y = 2) (hYA : Y.relIndex A = 4 * ry)
    (hBY : B.relIndex Y = 2 * r₂)
    (hAZ : A.relIndex Z = 2) (hZA : Z.relIndex A = 4 * rz)
    (hBZ : B.relIndex Z = 2 * r₂)
    (hXY : X.relIndex Y = rx * kXY) (hYX : Y.relIndex X = ry * kXY)
    (hXZ : X.relIndex Z = rx * kXZ) (hZX : Z.relIndex X = rz * kXZ)
    (hh : IsHarmonicCosetFamily ![a, b, x, y, z] ![A, B, X, Y, Z]) : False := by
  have hdAB := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hdAX := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdAY := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdAZ := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdBX := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdBY := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdBZ := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdXY := hh (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdXZ := hh (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hdAB hdAX hdAY hdAZ hdBX hdBY hdBZ hdXY hdXZ
  have hclaimY := p47_claim4_specialized A B X Y a b x y
    r₂ rx ry kXY hA hB hX hY hodd₂ hc₂x hc₂y hcxy
    hkXYpos hkXYlt hAX hXA hBX hXB hAY hYA hBY hXY
    (fun t ht ↦ hdAB t ht.1 ht.2) (fun t ht ↦ hdAX t ht.1 ht.2)
    (fun t ht ↦ hdAY t ht.1 ht.2) (fun t ht ↦ hdBX t ht.1 ht.2)
    (fun t ht ↦ hdBY t ht.1 ht.2) (fun t ht ↦ hdXY t ht.1 ht.2)
  have hclaimZ := p47_claim4_specialized A B X Z a b x z
    r₂ rx rz kXZ hA hB hX hZ hodd₂ hc₂x hc₂z hcxz
    hkXZpos hkXZlt hAX hXA hBX hXB hAZ hZA hBZ hXZ
    (fun t ht ↦ hdAB t ht.1 ht.2) (fun t ht ↦ hdAX t ht.1 ht.2)
    (fun t ht ↦ hdAZ t ht.1 ht.2) (fun t ht ↦ hdBX t ht.1 ht.2)
    (fun t ht ↦ hdBZ t ht.1 ht.2) (fun t ht ↦ hdXZ t ht.1 ht.2)
  rcases hclaimY.1 with hkY | hkY
  · rcases hclaimZ.1 with hkZ | hkZ
    · exact p47_mixedOnes_impossible A B X Y Z a b x y z r₂ rx ry rz
        hA hB hX hY hZ hodd₂ hc₂x hc₂y hc₂z hcxy hcxz hcyz
        hAX hXA hBX hXB
        (by simpa [hkY] using hXY) (by simpa [hkY] using hYX)
        (by simpa [hkZ] using hXZ) (by simpa [hkZ] using hZX) hh
    · exact p47_mixedThree_impossible A B X Z r₂ rx rz hA hB hZ hodd₂
        hAB hBA hAX hAZ hBX (by simpa [hkZ] using hZX)
  · exact p47_mixedThree_impossible A B X Y r₂ rx ry hA hB hY hodd₂
      hAB hBA hAX hAY hBX (by simpa [hkY] using hYX)

/-- Margolis--Schnabel Proposition 4.7 for finite groups, in its exact
index-three special form.  The six coprimality assumptions are written
explicitly so the detector bridge can instantiate this theorem without an
opaque aggregate hypothesis. -/
theorem margolisSchnabel_prop4_7_finite
    {G : Type u} [Group G] [Finite G]
    (g : Fin 5 → G) (U : Fin 5 → Subgroup G)
    (r₂ r₃ r₄ r₅ : ℕ)
    (h₁ : (U 0).index = 3)
    (h₂ : (U 1).index = 3 * r₂)
    (h₃ : (U 2).index = 6 * r₃)
    (h₄ : (U 3).index = 6 * r₄)
    (h₅ : (U 4).index = 6 * r₅)
    (hodd₂ : Odd r₂)
    (hc₂₃ : Nat.Coprime r₂ r₃) (hc₂₄ : Nat.Coprime r₂ r₄)
    (hc₂₅ : Nat.Coprime r₂ r₅) (hc₃₄ : Nat.Coprime r₃ r₄)
    (hc₃₅ : Nat.Coprime r₃ r₅) (hc₄₅ : Nat.Coprime r₄ r₅) :
    ¬ IsHarmonicCosetFamily g U := by
  intro hharmonic
  let a := g (0 : Fin 5)
  let b := g (1 : Fin 5)
  let c := g (2 : Fin 5)
  let d := g (3 : Fin 5)
  let e := g (4 : Fin 5)
  let A := U (0 : Fin 5)
  let B := U (1 : Fin 5)
  let C := U (2 : Fin 5)
  let D := U (3 : Fin 5)
  let E := U (4 : Fin 5)
  have hA : A.index = 3 := by simpa [A] using h₁
  have hB : B.index = 3 * r₂ := by simpa [B] using h₂
  have hC : C.index = 6 * r₃ := by simpa [C] using h₃
  have hD : D.index = 6 * r₄ := by simpa [D] using h₄
  have hE : E.index = 6 * r₅ := by simpa [E] using h₅
  have hh : IsHarmonicCosetFamily ![a, b, c, d, e] ![A, B, C, D, E] := by
    convert hharmonic using 1 <;> funext i <;> fin_cases i <;> rfl
  have hdAB := hh (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have hdAC := hh (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdAD := hh (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdAE := hh (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdBC := hh (i := (1 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have hdBD := hh (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdBE := hh (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdCD := hh (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have hdCE := hh (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have hdDE := hh (i := (3 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  simp at hdAB hdAC hdAD hdAE hdBC hdBD hdBE hdCD hdCE hdDE
  have hc₂_2₃ : Nat.Coprime r₂ (2 * r₃) :=
    hodd₂.coprime_two_right.mul_right hc₂₃
  have hc₂_2₄ : Nat.Coprime r₂ (2 * r₄) :=
    hodd₂.coprime_two_right.mul_right hc₂₄
  have hc₂_2₅ : Nat.Coprime r₂ (2 * r₅) :=
    hodd₂.coprime_two_right.mul_right hc₂₅
  rcases commonFactorPairData_of_disjoint A B a b (m := 3) (r := 1) (s := r₂)
      (by omega) (by omega) hB (by simp) (fun x hx ↦ hdAB x hx.1 hx.2) with
    ⟨kAB, hkABpos, hkABlt, hAB, hBA⟩
  rcases commonFactorPairData_of_disjoint A C a c (m := 3) (r := 1) (s := 2 * r₃)
      (by omega) (by omega) (by omega) (by simp) (fun x hx ↦ hdAC x hx.1 hx.2) with
    ⟨kAC, hkACpos, hkAClt, hAC, hCA⟩
  rcases commonFactorPairData_of_disjoint A D a d (m := 3) (r := 1) (s := 2 * r₄)
      (by omega) (by omega) (by omega) (by simp) (fun x hx ↦ hdAD x hx.1 hx.2) with
    ⟨kAD, hkADpos, hkADlt, hAD, hDA⟩
  rcases commonFactorPairData_of_disjoint A E a e (m := 3) (r := 1) (s := 2 * r₅)
      (by omega) (by omega) (by omega) (by simp) (fun x hx ↦ hdAE x hx.1 hx.2) with
    ⟨kAE, hkAEpos, hkAElt, hAE, hEA⟩
  rcases commonFactorPairData_of_disjoint B C b c (m := 3) (r := r₂) (s := 2 * r₃)
      (by omega) hB (by omega) hc₂_2₃ (fun x hx ↦ hdBC x hx.1 hx.2) with
    ⟨kBC, hkBCpos, hkBClt, hBC, hCB⟩
  rcases commonFactorPairData_of_disjoint B D b d (m := 3) (r := r₂) (s := 2 * r₄)
      (by omega) hB (by omega) hc₂_2₄ (fun x hx ↦ hdBD x hx.1 hx.2) with
    ⟨kBD, hkBDpos, hkBDlt, hBD, hDB⟩
  rcases commonFactorPairData_of_disjoint B E b e (m := 3) (r := r₂) (s := 2 * r₅)
      (by omega) hB (by omega) hc₂_2₅ (fun x hx ↦ hdBE x hx.1 hx.2) with
    ⟨kBE, hkBEpos, hkBElt, hBE, hEB⟩
  rcases commonFactorPairData_of_disjoint C D c d (m := 6) (r := r₃) (s := r₄)
      (by omega) hC hD hc₃₄ (fun x hx ↦ hdCD x hx.1 hx.2) with
    ⟨kCD, hkCDpos, hkCDlt, hCD, hDC⟩
  rcases commonFactorPairData_of_disjoint C E c e (m := 6) (r := r₃) (s := r₅)
      (by omega) hC hE hc₃₅ (fun x hx ↦ hdCE x hx.1 hx.2) with
    ⟨kCE, hkCEpos, hkCElt, hCE, hEC⟩
  rcases commonFactorPairData_of_disjoint D E d e (m := 6) (r := r₄) (s := r₅)
      (by omega) hD hE hc₄₅ (fun x hx ↦ hdDE x hx.1 hx.2) with
    ⟨kDE, hkDEpos, hkDElt, hDE, hED⟩
  rcases p47_claim1_specialized A B C D E a b c d e r₂ r₃ r₄ r₅
      kAB kAC kAD kAE kBC kBD kBE hA hB hC hD hE hodd₂
      hc₂₃ hc₂₄ hc₂₅ hc₃₄ hc₃₅ hc₄₅
      hkABpos hkABlt hkACpos hkAClt hkADpos hkADlt hkAEpos hkAElt
      hkBCpos hkBClt hkBDpos hkBDlt hkBEpos hkBElt
      (by simpa using hAB) hBA (by simpa using hAC) hCA
      (by simpa using hAD) hDA (by simpa using hAE) hEA
      hBC hCB hBD hDB hBE hEB hh with
    ⟨hkAB, hkC, hkD, hkE⟩
  subst kAB
  subst kBC
  subst kBD
  subst kBE
  have hkCcases : kAC = 1 ∨ kAC = 2 := by omega
  have hkDcases : kAD = 1 ∨ kAD = 2 := by omega
  have hkEcases : kAE = 1 ∨ kAE = 2 := by omega
  rcases hkCcases with rfl | rfl
  · rcases hkDcases with rfl | rfl
    · rcases hkEcases with rfl | rfl
      · exact p47_allOne_impossible A B C D E a b c d e r₂ r₃ r₄ r₅
          hA (by simpa using hAB) (by simpa [mul_comm] using hBA)
          (by simpa using hCA) (by simpa using hDA) (by simpa using hEA)
          hc₂₃ hc₂₄ hc₂₅ hc₃₄ hc₃₅ hc₄₅ hh
      · exact p47_twoOneOne_impossible A B C D E a b c d e
          r₂ r₃ r₄ r₅ kCE kDE hA hB hC hD hE hodd₂
          hc₂₃ hc₂₄ hc₂₅ hc₃₄ hc₃₅ hc₄₅
          hkCEpos hkCElt hkDEpos hkDElt
          (by simpa using hAC) (by simpa using hCA)
          (by simpa using hBC) (by simpa using hCB)
          (by simpa using hAD) (by simpa using hDA)
          (by simpa using hBD) (by simpa using hDB)
          (by simpa using hAE) (by omega) (by omega)
          hCE hDE hh
    · rcases hkEcases with rfl | rfl
      · let f : Fin 5 → Fin 5 := ![0, 1, 2, 4, 3]
        have hf : Function.Injective f := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
        have hh' : IsHarmonicCosetFamily ![a, b, c, e, d] ![A, B, C, E, D] := by
          convert p47_harmonic_reindex ![a, b, c, d, e] ![A, B, C, D, E] f hf hh
            using 1 <;> funext i <;> fin_cases i <;> rfl
        exact p47_twoOneOne_impossible A B C E D a b c e d
          r₂ r₃ r₅ r₄ kCD kDE hA hB hC hE hD hodd₂
          hc₂₃ hc₂₅ hc₂₄ hc₃₅ hc₃₄ hc₄₅.symm
          hkCDpos hkCDlt hkDEpos hkDElt
          (by simpa using hAC) (by simpa using hCA)
          (by simpa using hBC) (by simpa using hCB)
          (by simpa using hAE) (by simpa using hEA)
          (by simpa using hBE) (by simpa using hEB)
          (by simpa using hAD) (by omega) (by omega)
          hCD (by simpa using hED) hh'
      · exact p47_oneTwoTwo_impossible A B C D E a b c d e
          r₂ r₃ r₄ r₅ kCD kCE hA hB hC hD hE hodd₂
          hc₂₃ hc₂₄ hc₂₅ hc₃₄ hc₃₅ hc₄₅
          hkCDpos hkCDlt hkCEpos hkCElt
          (by simpa using hAB) (by simpa [mul_comm] using hBA)
          (by simpa using hAC) (by simpa using hCA)
          (by simpa using hBC) (by simpa using hCB)
          (by simpa using hAD) (by omega) (by omega)
          (by simpa using hAE) (by omega) (by omega)
          hCD hDC hCE hEC hh
  · rcases hkDcases with rfl | rfl
    · rcases hkEcases with rfl | rfl
      · let f : Fin 5 → Fin 5 := ![0, 1, 3, 4, 2]
        have hf : Function.Injective f := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
        have hh' : IsHarmonicCosetFamily ![a, b, d, e, c] ![A, B, D, E, C] := by
          convert p47_harmonic_reindex ![a, b, c, d, e] ![A, B, C, D, E] f hf hh
            using 1 <;> funext i <;> fin_cases i <;> rfl
        exact p47_twoOneOne_impossible A B D E C a b d e c
          r₂ r₄ r₅ r₃ kCD kCE hA hB hD hE hC hodd₂
          hc₂₄ hc₂₅ hc₂₃ hc₄₅ hc₃₄.symm hc₃₅.symm
          hkCDpos hkCDlt hkCEpos hkCElt
          (by simpa using hAD) (by simpa using hDA)
          (by simpa using hBD) (by simpa using hDB)
          (by simpa using hAE) (by simpa using hEA)
          (by simpa using hBE) (by simpa using hEB)
          (by simpa using hAC) (by omega) (by omega)
          (by simpa using hDC) (by simpa using hEC) hh'
      · let f : Fin 5 → Fin 5 := ![0, 1, 3, 2, 4]
        have hf : Function.Injective f := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
        have hh' : IsHarmonicCosetFamily ![a, b, d, c, e] ![A, B, D, C, E] := by
          convert p47_harmonic_reindex ![a, b, c, d, e] ![A, B, C, D, E] f hf hh
            using 1 <;> funext i <;> fin_cases i <;> rfl
        exact p47_oneTwoTwo_impossible A B D C E a b d c e
          r₂ r₄ r₃ r₅ kCD kDE hA hB hD hC hE hodd₂
          hc₂₄ hc₂₃ hc₂₅ hc₃₄.symm hc₄₅ hc₃₅
          hkCDpos hkCDlt hkDEpos hkDElt
          (by simpa using hAB) (by simpa [mul_comm] using hBA)
          (by simpa using hAD) (by simpa using hDA)
          (by simpa using hBD) (by simpa using hDB)
          (by simpa using hAC) (by omega) (by omega)
          (by simpa using hAE) (by omega) (by omega)
          hDC hCD hDE hED hh'
    · rcases hkEcases with rfl | rfl
      · let f : Fin 5 → Fin 5 := ![0, 1, 4, 2, 3]
        have hf : Function.Injective f := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
        have hh' : IsHarmonicCosetFamily ![a, b, e, c, d] ![A, B, E, C, D] := by
          convert p47_harmonic_reindex ![a, b, c, d, e] ![A, B, C, D, E] f hf hh
            using 1 <;> funext i <;> fin_cases i <;> rfl
        exact p47_oneTwoTwo_impossible A B E C D a b e c d
          r₂ r₅ r₃ r₄ kCE kDE hA hB hE hC hD hodd₂
          hc₂₅ hc₂₃ hc₂₄ hc₃₅.symm hc₄₅.symm hc₃₄
          hkCEpos hkCElt hkDEpos hkDElt
          (by simpa using hAB) (by simpa [mul_comm] using hBA)
          (by simpa using hAE) (by simpa using hEA)
          (by simpa using hBE) (by simpa using hEB)
          (by simpa using hAC) (by omega) (by omega)
          (by simpa using hAD) (by omega) (by omega)
          hEC hCE hED hDE hh'
      · exact p47_allTwo_impossible A B C D E a b c d e r₂ r₃ r₄ r₅
          hA (by simpa [mul_comm] using hBA)
          (by simpa using hAC) (by simpa using hAD) (by simpa using hAE)
          (by omega) (by omega) (by omega)
          hodd₂ hc₂₃ hc₂₄ hc₂₅ hc₃₄ hc₃₅ hc₄₅ hh

end ErdosProblems.E274
