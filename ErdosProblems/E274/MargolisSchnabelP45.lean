import ErdosProblems.E274.FiniteHarmonicCore

/-!
# Margolis--Schnabel Proposition 4.5

Finite-group formalization of the obstruction to a harmonic index tuple
`(2*r₁, 4*r₂, 4*r₃, 4*r₄)` when `r₁` is odd and all residuals are
pairwise coprime.
-/

namespace ErdosProblems.E274

open scoped Pointwise

universe u

private theorem odd_coprime_two_mul
    {r s : ℕ} (hodd : r % 2 = 1) (hcop : Nat.Coprime r s) :
    Nat.Coprime r (2 * s) := by
  have hOdd : Odd r := Nat.odd_iff.mpr hodd
  exact hOdd.coprime_two_right.mul_right hcop

/-- The mixed `(2*r,4*s)` instance of Lemma 4.1. -/
private theorem mixedPairData
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) (a b : G) {r s : ℕ}
    (hU : U.index = 2 * r) (hV : V.index = 4 * s)
    (hodd : r % 2 = 1) (hcop : Nat.Coprime r s)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    U.relIndex V = r ∧ V.relIndex U = 2 * s ∧
      2 * Nat.card ((U : Set G) * (V : Set G)) = Nat.card G ∧
      2 * Nat.card ((V : Set G) * (U : Set G)) = Nat.card G := by
  have hcop' := odd_coprime_two_mul hodd hcop
  have hV' : V.index = 2 * (2 * s) := by omega
  have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases exists_relIndex_eq_residual_mul_lt_commonFactor
      U V a b (m := 2) (r := r) (s := 2 * s) (by omega)
      hU hV' hcop' hdisjoint hUfinite with ⟨k, hk, hkpos, hklt⟩
  have hkone : k = 1 := by omega
  have hrelUV : U.relIndex V = r := by simpa [hkone] using hk
  rcases exists_relIndex_eq_residual_mul_lt_commonFactor
      V U b a (m := 2) (r := 2 * s) (s := r) (by omega)
      hV' hU hcop'.symm
      (fun x hx ↦ hdisjoint x ⟨hx.2, hx.1⟩) hVfinite with
    ⟨l, hl, hlpos, hllt⟩
  have hlone : l = 1 := by omega
  have hrelVU : V.relIndex U = 2 * s := by simpa [hlone] using hl
  have hhalfUV :
      2 * Nat.card ((U : Set G) * (V : Set G)) = Nat.card G := by
    simpa using commonFactor_mul_natCard_subgroup_mul_eq
      U V (k := 1) hV' (by simpa using hrelVU)
  have hhalfVU :
      2 * Nat.card ((V : Set G) * (U : Set G)) = Nat.card G := by
    simpa using commonFactor_mul_natCard_subgroup_mul_eq
      V U (k := 1) hU (by simpa using hrelUV)
  exact ⟨hrelUV, hrelVU, hhalfUV, hhalfVU⟩

/-- A pair of harmonic `(4*r,4*s)` cells has one common intersection
multiplier `k ∈ {1,2,3}` in both relative-index orientations. -/
private theorem fourPairMultiplier
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) (a b : G) {r s : ℕ}
    (hU : U.index = 4 * r) (hV : V.index = 4 * s)
    (hcop : Nat.Coprime r s)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    ∃ k : ℕ, (k = 1 ∨ k = 2 ∨ k = 3) ∧
      U.relIndex V = r * k ∧ V.relIndex U = s * k ∧
      4 * Nat.card ((U : Set G) * (V : Set G)) = k * Nat.card G := by
  have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases exists_relIndex_eq_residual_mul_lt_commonFactor
      U V a b (m := 4) (r := r) (s := s) (by omega)
      hU hV hcop hdisjoint hUfinite with ⟨k, hk, hkpos, hklt⟩
  rcases exists_relIndex_eq_residual_mul_lt_commonFactor
      V U b a (m := 4) (r := s) (s := r) (by omega)
      hV hU hcop.symm (fun x hx ↦ hdisjoint x ⟨hx.2, hx.1⟩) hVfinite with
    ⟨l, hl, hlpos, hllt⟩
  have hsame : k = l := by
    have hinter₁ : U.relIndex V * V.index = (U ⊓ V).index := by
      simpa [Subgroup.inf_relIndex_right] using
        (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
    have hinter₂ : V.relIndex U * U.index = (U ⊓ V).index := by
      rw [inf_comm]
      simpa [Subgroup.inf_relIndex_right] using
        (Subgroup.relIndex_mul_index (H := V ⊓ U) (K := U) inf_le_right)
    have heq : (4 * (r * s)) * k = (4 * (r * s)) * l := by
      calc
        (4 * (r * s)) * k = (r * k) * (4 * s) := by ring
        _ = U.relIndex V * V.index := by rw [hk, hV]
        _ = (U ⊓ V).index := hinter₁
        _ = V.relIndex U * U.index := hinter₂.symm
        _ = (s * l) * (4 * r) := by rw [hl, hU]
        _ = (4 * (r * s)) * l := by ring
    have hrpos : 0 < r := by
      by_contra hr
      have : r = 0 := Nat.eq_zero_of_not_pos hr
      exact hUfinite (by simp [hU, this])
    have hspos : 0 < s := by
      by_contra hs
      have : s = 0 := Nat.eq_zero_of_not_pos hs
      exact hVfinite (by simp [hV, this])
    exact Nat.mul_left_cancel (by positivity) heq
  subst l
  refine ⟨k, by omega, hk, hl, ?_⟩
  exact commonFactor_mul_natCard_subgroup_mul_eq U V hV hl

private theorem reverseRelIndex_of_commonFactor
    {G : Type u} [Group G] (U V : Subgroup G)
    {m r s k : ℕ} (hU : U.index = m * r) (hV : V.index = m * s)
    (hmr : 0 < m * r) (hforward : U.relIndex V = r * k) :
    V.relIndex U = s * k := by
  have hinterU : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hinterV : V.relIndex U * U.index = (U ⊓ V).index := by
    rw [inf_comm]
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := V ⊓ U) (K := U) inf_le_right)
  have hmul : (m * r) * (s * k) = (m * r) * V.relIndex U := by
    calc
      (m * r) * (s * k) = (r * k) * (m * s) := by ring
      _ = (U ⊓ V).index := by rw [← hinterU, hforward, hV]
      _ = V.relIndex U * (m * r) := by rw [← hinterV, hU]
      _ = (m * r) * V.relIndex U := by ring
  exact Nat.mul_left_cancel hmr hmul.symm

private theorem product_subset_product_of_le_right
    {G : Type u} [Group G] (U V W : Subgroup G) (hVW : V ≤ W) :
    (U : Set G) * (V : Set G) ⊆ (U : Set G) * (W : Set G) := by
  rintro x ⟨u, hu, v, hv, rfl⟩
  exact ⟨u, hu, v, hVW hv, rfl⟩

private theorem doubleCoset_subset_inter_products
    {G : Type u} [Group G] (U V W : Subgroup G) (x : G)
    (hxV : x ∈ (U : Set G) * (V : Set G))
    (hxW : x ∈ (U : Set G) * (W : Set G)) :
    DoubleCoset.doubleCoset x U (V ⊓ W) ⊆
      ((U : Set G) * (V : Set G)) ∩
        ((U : Set G) * (W : Set G)) := by
  rintro y hy
  rcases DoubleCoset.mem_doubleCoset.mp hy with ⟨u, hu, t, ht, rfl⟩
  rcases hxV with ⟨uV, huV, v, hv, huv⟩
  rcases hxW with ⟨uW, huW, w, hw, huw⟩
  constructor
  · refine ⟨u * uV, U.mul_mem hu huV, v * t, V.mul_mem hv ht.1, ?_⟩
    rw [← huv]
    simp [mul_assoc]
  · refine ⟨u * uW, U.mul_mem hu huW, w * t, W.mul_mem hw ht.2, ?_⟩
    rw [← huw]
    simp [mul_assoc]

/-- Margolis--Schnabel Lemma 4.4, expressed using `relIndex` multipliers.
The final two equalities are division-free versions of the source's
`|U₂(U₁ ∩ U₃)| = |U₂U₁ ∩ U₂U₃| = |G|/4`. -/
theorem margolisSchnabelLemma44
    {G : Type u} [Group G] [Finite G]
    (U₁ U₂ U₃ : Subgroup G) (g₁ g₂ g₃ : G)
    (r₁ r₂ r₃ : ℕ)
    (hU₁ : U₁.index = 2 * r₁)
    (hU₂ : U₂.index = 4 * r₂)
    (hU₃ : U₃.index = 4 * r₃)
    (hodd : r₁ % 2 = 1)
    (h12 : Nat.Coprime r₁ r₂)
    (h13 : Nat.Coprime r₁ r₃)
    (h23 : Nat.Coprime r₂ r₃)
    (hharmonic : IsHarmonicCosetFamily
      ![g₁, g₂, g₃] ![U₁, U₂, U₃]) :
    U₂.relIndex U₃ ≠ r₂ * 2 ∧
      (U₂.relIndex U₃ = r₂ * 3 →
        3 ∣ r₁ ∧
          4 * Nat.card ((U₂ : Set G) * ((U₁ ⊓ U₃ : Subgroup G) : Set G)) =
            Nat.card G ∧
          4 *
            (((U₂ : Set G) * (U₁ : Set G)) ∩
              ((U₂ : Set G) * (U₃ : Set G))).ncard = Nat.card G) := by
  classical
  have hd12 := hharmonic (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  have hd13 := hharmonic (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  have hd23 := hharmonic (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  simp at hd12 hd13 hd23
  have hU₁finite : U₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hU₂finite : U₂.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hU₃finite : U₃.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hr₁pos : 0 < r₁ := by
    by_contra h
    have : r₁ = 0 := Nat.eq_zero_of_not_pos h
    exact hU₁finite (by simp [hU₁, this])
  have hr₂pos : 0 < r₂ := by
    by_contra h
    have : r₂ = 0 := Nat.eq_zero_of_not_pos h
    exact hU₂finite (by simp [hU₂, this])
  have hr₃pos : 0 < r₃ := by
    by_contra h
    have : r₃ = 0 := Nat.eq_zero_of_not_pos h
    exact hU₃finite (by simp [hU₃, this])
  rcases mixedPairData U₁ U₂ g₁ g₂ hU₁ hU₂ hodd h12
      (fun x hx ↦ hd12 x hx.1 hx.2) with
    ⟨hrel12, hrel21, hhalf12, hhalf21⟩
  rcases mixedPairData U₁ U₃ g₁ g₃ hU₁ hU₃ hodd h13
      (fun x hx ↦ hd13 x hx.1 hx.2) with
    ⟨hrel13, hrel31, hhalf13, hhalf31⟩
  have hcop_r₁_four : Nat.Coprime r₁ 4 := by
    have hOdd : Odd r₁ := Nat.odd_iff.mpr hodd
    simpa using hOdd.coprime_two_right.pow_right 2
  have hcop_r₁_four23 : Nat.Coprime r₁ (4 * r₂ * r₃) :=
    (hcop_r₁_four.mul_right h12).mul_right h13
  constructor
  · intro hrel23two
    have hrel32two : U₃.relIndex U₂ = r₃ * 2 :=
      reverseRelIndex_of_commonFactor U₂ U₃ hU₂ hU₃ (by positivity) hrel23two
    let T : Subgroup G := U₂ ⊓ U₃
    have hTindex : T.index = 2 * (4 * r₂ * r₃) := by
      calc
        T.index = U₂.relIndex U₃ * U₃.index := by
          simpa [T, Subgroup.inf_relIndex_right] using
            (Subgroup.relIndex_mul_index (H := U₂ ⊓ U₃) (K := U₃)
              inf_le_right).symm
        _ = (r₂ * 2) * (4 * r₃) := by rw [hrel23two, hU₃]
        _ = 2 * (4 * r₂ * r₃) := by ring
    have hTfinite : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases exists_relIndex_eq_residual_mul T U₁ (m := 2)
        (r := 4 * r₂ * r₃) (s := r₁) (by omega) hTindex hU₁
        hcop_r₁_four23.symm hTfinite with ⟨k, hk, hkpos⟩
    have hnorm :
        2 * Nat.card ((U₁ : Set G) * (T : Set G)) = k * Nat.card G :=
      commonFactor_mul_natCard_subgroup_mul_eq U₁ T hTindex hk
    have hsub12 : (U₁ : Set G) * (T : Set G) ⊆
        (U₁ : Set G) * (U₂ : Set G) :=
      product_subset_product_of_le_right U₁ T U₂ inf_le_left
    have hsub13 : (U₁ : Set G) * (T : Set G) ⊆
        (U₁ : Set G) * (U₃ : Set G) :=
      product_subset_product_of_le_right U₁ T U₃ inf_le_right
    have hcardle12 :
        Nat.card ((U₁ : Set G) * (T : Set G)) ≤
          Nat.card ((U₁ : Set G) * (U₂ : Set G)) := by
      simpa only [Nat.card_coe_set_eq] using
        Set.ncard_le_ncard hsub12 (Set.toFinite _)
    have hinnerHalf :
        2 * Nat.card ((U₁ : Set G) * (T : Set G)) = Nat.card G := by
      have hkone : 1 ≤ k := hkpos
      have hupper :
          2 * Nat.card ((U₁ : Set G) * (T : Set G)) ≤ Nat.card G := by
        nlinarith [hcardle12]
      have hlower : Nat.card G ≤
          2 * Nat.card ((U₁ : Set G) * (T : Set G)) := by
        calc
          Nat.card G = 1 * Nat.card G := by simp
          _ ≤ k * Nat.card G := Nat.mul_le_mul_right _ hkone
          _ = 2 * Nat.card ((U₁ : Set G) * (T : Set G)) := hnorm.symm
      omega
    have heq12 : (U₁ : Set G) * (T : Set G) =
        (U₁ : Set G) * (U₂ : Set G) := by
      apply Set.eq_of_subset_of_ncard_le hsub12
      simpa only [Nat.card_coe_set_eq] using (by omega :
        Nat.card ((U₁ : Set G) * (U₂ : Set G)) ≤
          Nat.card ((U₁ : Set G) * (T : Set G)))
    have heq13 : (U₁ : Set G) * (T : Set G) =
        (U₁ : Set G) * (U₃ : Set G) := by
      apply Set.eq_of_subset_of_ncard_le hsub13
      simpa only [Nat.card_coe_set_eq] using (by omega :
        Nat.card ((U₁ : Set G) * (U₃ : Set G)) ≤
          Nat.card ((U₁ : Set G) * (T : Set G)))
    have heq : (U₁ : Set G) * (U₂ : Set G) =
        (U₁ : Set G) * (U₃ : Set G) := heq12.symm.trans heq13
    have hincl : (U₂ : Set G) * (U₁ : Set G) ⊆
        (U₃ : Set G) * (U₁ : Set G) := by
      exact Set.Subset.rfl.trans_eq
        (subgroup_mul_right_eq_of_mul_left_eq U₁ U₂ U₃ heq)
    have hhalf32 :
        2 * Nat.card ((U₃ : Set G) * (U₂ : Set G)) = Nat.card G := by
      have hfour := commonFactor_mul_natCard_subgroup_mul_eq
        U₃ U₂ (k := 2) hU₂ hrel23two
      omega
    exact not_harmonic_three_of_half_products U₁ U₃ U₂ g₁ g₃ g₂
      (fun x hx ↦ hd13 x hx.1 hx.2)
      (fun x hx ↦ hd12 x hx.1 hx.2)
      (fun x hx ↦ hd23 x hx.2 hx.1)
      hincl hhalf12 hhalf32
  · intro hrel23three
    have hrel32three : U₃.relIndex U₂ = r₃ * 3 :=
      reverseRelIndex_of_commonFactor U₂ U₃ hU₂ hU₃ (by positivity) hrel23three
    let T : Subgroup G := U₁ ⊓ U₃
    have hTindex : T.index = 4 * (r₁ * r₃) := by
      calc
        T.index = U₁.relIndex U₃ * U₃.index := by
          simpa [T, Subgroup.inf_relIndex_right] using
            (Subgroup.relIndex_mul_index (H := U₁ ⊓ U₃) (K := U₃)
              inf_le_right).symm
        _ = r₁ * (4 * r₃) := by rw [hrel13, hU₃]
        _ = 4 * (r₁ * r₃) := by ring
    have hcop₂T : Nat.Coprime r₂ (r₁ * r₃) :=
      h12.symm.mul_right h23
    have hTfinite : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases exists_relIndex_eq_residual_mul T U₂ (m := 4)
        (r := r₁ * r₃) (s := r₂) (by omega) hTindex hU₂
        hcop₂T.symm hTfinite with ⟨k, hk, hkpos⟩
    have hnorm :
        4 * Nat.card ((U₂ : Set G) * (T : Set G)) = k * Nat.card G :=
      commonFactor_mul_natCard_subgroup_mul_eq U₂ T hTindex hk
    have hsub21 : (U₂ : Set G) * (T : Set G) ⊆
        (U₂ : Set G) * (U₁ : Set G) :=
      product_subset_product_of_le_right U₂ T U₁ inf_le_left
    have hsub23 : (U₂ : Set G) * (T : Set G) ⊆
        (U₂ : Set G) * (U₃ : Set G) :=
      product_subset_product_of_le_right U₂ T U₃ inf_le_right
    have hcardle21 :
        Nat.card ((U₂ : Set G) * (T : Set G)) ≤
          Nat.card ((U₂ : Set G) * (U₁ : Set G)) := by
      simpa only [Nat.card_coe_set_eq] using
        Set.ncard_le_ncard hsub21 (Set.toFinite _)
    have hk_le_two : k ≤ 2 := by
      have hfour_le := Nat.mul_le_mul_left 4 hcardle21
      have hkG_le : k * Nat.card G ≤ 2 * Nat.card G := by
        calc
          k * Nat.card G =
              4 * Nat.card ((U₂ : Set G) * (T : Set G)) := hnorm.symm
          _ ≤ 4 * Nat.card ((U₂ : Set G) * (U₁ : Set G)) := hfour_le
          _ = 2 * Nat.card G := by omega
      exact Nat.le_of_mul_le_mul_right hkG_le Nat.card_pos
    have hthree_dvd_r₁ : 3 ∣ r₁ := by
      have hDdiv : (U₂ ⊓ U₃).index ∣ (T ⊓ U₂).index := by
        apply Subgroup.index_dvd_of_le
        intro x hx
        exact ⟨hx.2, hx.1.2⟩
      have hDindex : (T ⊓ U₂).index =
          4 * (r₁ * r₂ * r₃ * k) := by
        calc
          (T ⊓ U₂).index = T.relIndex U₂ * U₂.index := by
            simpa [Subgroup.inf_relIndex_right] using
              (Subgroup.relIndex_mul_index (H := T ⊓ U₂) (K := U₂)
                inf_le_right).symm
          _ = ((r₁ * r₃) * k) * (4 * r₂) := by rw [hk, hU₂]
          _ = 4 * (r₁ * r₂ * r₃ * k) := by ring
      have h23index : (U₂ ⊓ U₃).index = 12 * (r₂ * r₃) := by
        calc
          (U₂ ⊓ U₃).index = U₂.relIndex U₃ * U₃.index := by
            simpa [Subgroup.inf_relIndex_right] using
              (Subgroup.relIndex_mul_index (H := U₂ ⊓ U₃) (K := U₃)
                inf_le_right).symm
          _ = (r₂ * 3) * (4 * r₃) := by rw [hrel23three, hU₃]
          _ = 12 * (r₂ * r₃) := by ring
      rw [h23index, hDindex] at hDdiv
      have hcancel : 3 ∣ r₁ * k := by
        have hfactorPos : 0 < 4 * (r₂ * r₃) := by positivity
        apply Nat.dvd_of_mul_dvd_mul_right hfactorPos
        simpa [mul_assoc, mul_left_comm, mul_comm] using hDdiv
      by_contra hnot
      have hcop3 : Nat.Coprime 3 r₁ :=
        Nat.prime_three.coprime_iff_not_dvd.mpr hnot
      have h3k : 3 ∣ k := hcop3.dvd_of_dvd_mul_left hcancel
      have hthree_le : 3 ≤ k := Nat.le_of_dvd hkpos h3k
      omega
    have hkone : k = 1 := by
      have hk_cases : k = 1 ∨ k = 2 := by omega
      rcases hk_cases with rfl | rfl
      · rfl
      · have hinnerHalf :
            2 * Nat.card ((U₂ : Set G) * (T : Set G)) = Nat.card G := by
          omega
        have heq21 : (U₂ : Set G) * (T : Set G) =
            (U₂ : Set G) * (U₁ : Set G) := by
          apply Set.eq_of_subset_of_ncard_le hsub21
          simpa only [Nat.card_coe_set_eq] using (by omega :
            Nat.card ((U₂ : Set G) * (U₁ : Set G)) ≤
              Nat.card ((U₂ : Set G) * (T : Set G)))
        have hincl21_23 : (U₂ : Set G) * (U₁ : Set G) ⊆
            (U₂ : Set G) * (U₃ : Set G) := by
          rw [← heq21]
          exact hsub23
        have hincl12_32 : (U₁ : Set G) * (U₂ : Set G) ⊆
            (U₃ : Set G) * (U₂ : Set G) :=
          subgroup_mul_right_subset_of_mul_left_subset
            U₂ U₁ U₃ hincl21_23
        have hcover : Nat.card G ≤
            Nat.card ((U₂ : Set G) * (U₁ : Set G)) +
              Nat.card ((U₃ : Set G) * (U₁ : Set G)) := by omega
        exact (not_harmonic_three_of_product_cover U₂ U₃ U₁ g₂ g₃ g₁
          (fun x hx ↦ hd23 x hx.1 hx.2)
          (fun x hx ↦ hd12 x hx.2 hx.1)
          (fun x hx ↦ hd13 x hx.2 hx.1)
          hincl12_32 hcover).elim
    subst k
    have hquarterInner :
        4 * Nat.card ((U₂ : Set G) * (T : Set G)) = Nat.card G := by
      simpa using hnorm
    let X : Set G :=
      ((U₂ : Set G) * (U₁ : Set G)) ∩
        ((U₂ : Set G) * (U₃ : Set G))
    have hinnerX : (U₂ : Set G) * (T : Set G) ⊆ X := by
      intro x hx
      exact ⟨hsub21 hx, hsub23 hx⟩
    have hXinner : X ⊆ (U₂ : Set G) * (T : Set G) := by
      intro x hx
      by_contra hxnot
      let D : Set G := DoubleCoset.doubleCoset x U₂ T
      have hDX : D ⊆ X := by
        exact doubleCoset_subset_inter_products U₂ U₁ U₃ x hx.1 hx.2
      have hDlower : Nat.card G ≤ 4 * D.ncard := by
        exact natCard_le_commonFactor_mul_ncard_doubleCoset
          U₂ T x (m := 4) (r := r₂) (s := r₁ * r₃)
          (by omega) hU₂ hTindex hcop₂T
      have hinnerDouble : DoubleCoset.doubleCoset 1 U₂ T =
          (U₂ : Set G) * (T : Set G) := by
        simp [DoubleCoset.doubleCoset]
      have hdisj : Disjoint ((U₂ : Set G) * (T : Set G)) D := by
        rw [← hinnerDouble]
        by_contra hnotdisj
        have heq := DoubleCoset.eq_of_not_disjoint hnotdisj
        have hxD : x ∈ D := DoubleCoset.mem_doubleCoset_self U₂ T x
        have hxInner : x ∈ (U₂ : Set G) * (T : Set G) := by
          rw [← hinnerDouble, heq]
          exact hxD
        exact hxnot hxInner
      have hunionX : ((U₂ : Set G) * (T : Set G)) ∪ D ⊆ X :=
        Set.union_subset hinnerX hDX
      have hunionCard :
          (((U₂ : Set G) * (T : Set G)) ∪ D).ncard =
            ((U₂ : Set G) * (T : Set G)).ncard + D.ncard :=
        Set.ncard_union_eq hdisj
      have hinner_le_D :
          ((U₂ : Set G) * (T : Set G)).ncard ≤ D.ncard := by
        have hq : 4 * ((U₂ : Set G) * (T : Set G)).ncard = Nat.card G := by
          simpa only [Nat.card_coe_set_eq] using hquarterInner
        omega
      have hAcard :
          ((U₂ : Set G) * (U₁ : Set G)).ncard =
            2 * ((U₂ : Set G) * (T : Set G)).ncard := by
        have hhalf21' :
            2 * ((U₂ : Set G) * (U₁ : Set G)).ncard = Nat.card G := by
          simpa only [Nat.card_coe_set_eq] using hhalf21
        have hquarterInner' :
            4 * ((U₂ : Set G) * (T : Set G)).ncard = Nat.card G := by
          simpa only [Nat.card_coe_set_eq] using hquarterInner
        omega
      have hunionA : ((U₂ : Set G) * (U₁ : Set G)) ⊆
          ((U₂ : Set G) * (T : Set G)) ∪ D := by
        have hunionSubsetA : ((U₂ : Set G) * (T : Set G)) ∪ D ⊆
            (U₂ : Set G) * (U₁ : Set G) := fun y hy ↦ (hunionX hy).1
        have heq : ((U₂ : Set G) * (T : Set G)) ∪ D =
            (U₂ : Set G) * (U₁ : Set G) := by
          apply Set.eq_of_subset_of_ncard_le hunionSubsetA
          rw [hunionCard, hAcard]
          omega
        exact heq.symm.subset
      have hA_X : (U₂ : Set G) * (U₁ : Set G) ⊆ X :=
        hunionA.trans hunionX
      have hA_B : (U₂ : Set G) * (U₁ : Set G) ⊆
          (U₂ : Set G) * (U₃ : Set G) := fun y hy ↦ (hA_X hy).2
      have hinv : (U₁ : Set G) * (U₂ : Set G) ⊆
          (U₃ : Set G) * (U₂ : Set G) :=
        subgroup_mul_right_subset_of_mul_left_subset U₂ U₁ U₃ hA_B
      have hcover : Nat.card G ≤
          Nat.card ((U₂ : Set G) * (U₁ : Set G)) +
            Nat.card ((U₃ : Set G) * (U₁ : Set G)) := by omega
      exact not_harmonic_three_of_product_cover U₂ U₃ U₁ g₂ g₃ g₁
        (fun y hy ↦ hd23 y hy.1 hy.2)
        (fun y hy ↦ hd12 y hy.2 hy.1)
        (fun y hy ↦ hd13 y hy.2 hy.1)
        hinv hcover
    have hXeq : X = (U₂ : Set G) * (T : Set G) :=
      Set.Subset.antisymm hXinner hinnerX
    refine ⟨hthree_dvd_r₁, hquarterInner, ?_⟩
    rw [show (((U₂ : Set G) * (U₁ : Set G)) ∩
      ((U₂ : Set G) * (U₃ : Set G))) = X by rfl, hXeq]
    exact hquarterInner

private theorem alphaOneIntersection_mul_eq_high
    {G : Type u} [Group G] [Finite G]
    (Uj V Ui : Subgroup G) {rj rv ri : ℕ}
    (hUj : Uj.index = 4 * rj) (hV : V.index = 4 * rv)
    (hUi : Ui.index = 4 * ri)
    (hij : Nat.Coprime ri rj) (hiv : Nat.Coprime ri rv)
    (hrelUjV : Uj.relIndex V = rj)
    (hrelUiV : Ui.relIndex V = ri) :
    (((Uj ⊓ V : Subgroup G) : Set G) * (Ui : Set G)) =
      (V : Set G) * (Ui : Set G) := by
  let T : Subgroup G := Uj ⊓ V
  have hTindex : T.index = 4 * (rj * rv) := by
    calc
      T.index = Uj.relIndex V * V.index := by
        simpa [T, Subgroup.inf_relIndex_right] using
          (Subgroup.relIndex_mul_index (H := Uj ⊓ V) (K := V)
            inf_le_right).symm
      _ = rj * (4 * rv) := by rw [hrelUjV, hV]
      _ = 4 * (rj * rv) := by ring
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
  have hraw : 4 * ri ∣ Ui.relIndex T * (4 * (rj * rv)) := by
    rw [← hinter, hUi, hTindex] at hdivIndex
    exact hdivIndex
  have hcancel : ri ∣ Ui.relIndex T * (rj * rv) := by
    apply Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 4)
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
      (V : Set G) * (Ui : Set G) := by
    rintro x ⟨t, ht, i, hi, rfl⟩
    exact ⟨t, ht.2, i, hi, rfl⟩
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    natCard_subgroup_mul, natCard_subgroup_mul, hrel, hrelUiV]

private theorem alphaOneIntersection_mul_eq_low
    {G : Type u} [Group G] [Finite G]
    (Uj V Ui : Subgroup G) {rj rv ri : ℕ}
    (hUj : Uj.index = 4 * rj) (hV : V.index = 4 * rv)
    (hUi : Ui.index = 2 * ri) (hodd : ri % 2 = 1)
    (hij : Nat.Coprime ri rj) (hiv : Nat.Coprime ri rv)
    (hrelUjV : Uj.relIndex V = rj)
    (hrelUiV : Ui.relIndex V = ri) :
    (((Uj ⊓ V : Subgroup G) : Set G) * (Ui : Set G)) =
      (V : Set G) * (Ui : Set G) := by
  let T : Subgroup G := Uj ⊓ V
  have hTindex : T.index = 4 * (rj * rv) := by
    calc
      T.index = Uj.relIndex V * V.index := by
        simpa [T, Subgroup.inf_relIndex_right] using
          (Subgroup.relIndex_mul_index (H := Uj ⊓ V) (K := V)
            inf_le_right).symm
      _ = rj * (4 * rv) := by rw [hrelUjV, hV]
      _ = 4 * (rj * rv) := by ring
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
  have hraw : 2 * ri ∣ Ui.relIndex T * (4 * (rj * rv)) := by
    rw [← hinter, hUi, hTindex] at hdivIndex
    exact hdivIndex
  have hcancel : ri ∣ Ui.relIndex T * (2 * (rj * rv)) := by
    have hraw' : 2 * ri ∣ 2 * (Ui.relIndex T * (2 * (rj * rv))) := by
      convert hraw using 1 <;> ring
    apply Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2)
    exact hraw'
  have hOdd : Odd ri := Nat.odd_iff.mpr hodd
  have hcop : Nat.Coprime ri (2 * (rj * rv)) :=
    hOdd.coprime_two_right.mul_right (hij.mul_right hiv)
  have hdiv : ri ∣ Ui.relIndex T :=
    hcop.dvd_of_dvd_mul_right hcancel
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
  have hsubset' : (T : Set G) * (Ui : Set G) ⊆
      (V : Set G) * (Ui : Set G) := by
    rintro x ⟨t, ht, i, hi, rfl⟩
    exact ⟨t, ht.2, i, hi, rfl⟩
  apply Set.eq_of_subset_of_ncard_le hsubset'
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    natCard_subgroup_mul, natCard_subgroup_mul, hrel, hrelUiV]

private theorem p45_thickened_disjoint
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
  have hvpart : v' * v⁻¹ ∈ V := V.mul_mem hv' (V.inv_mem hv)
  have hsmall : (v' * v⁻¹) * ui⁻¹ ∈
      (V : Set G) * (Ui : Set G) :=
    ⟨v' * v⁻¹, hvpart, ui⁻¹, Ui.inv_mem hui, rfl⟩
  rcases hsubset hsmall with ⟨uj', huj', ui', hui', heqSmall⟩
  have hnot := inv_mul_notMem_mul_of_disjoint_leftCosets Uj Ui gj gi
    (by
      intro z hz
      exact hij z ⟨hz.2, hz.1⟩)
  apply hnot
  refine ⟨uj * uj', Uj.mul_mem huj huj', ui', hui', ?_⟩
  have heq : gi * (ui * v) = gj * (uj * v') := hi.trans hj.symm
  have hji : gj⁻¹ * gi = uj * ((v' * v⁻¹) * ui⁻¹) := by
    have heq' := congrArg (fun z ↦ gj⁻¹ * z * v⁻¹ * ui⁻¹) heq
    simpa [mul_assoc] using heq'
  calc
    (uj * uj') * ui' = uj * (uj' * ui') := by simp [mul_assoc]
    _ = uj * ((v' * v⁻¹) * ui⁻¹) := by
      exact congrArg (fun z ↦ uj * z) heqSmall
    _ = gj⁻¹ * gi := hji.symm

/-- The `(1/2,1/4,1/4)` instance of source Proposition 3.8 used by
Proposition 4.5. -/
private theorem p45_proposition38_mixed_anchor
    {G : Type u} [Group G] [Finite G]
    (U₀ U₁ U₂ V : Subgroup G) (g₀ g₁ g₂ gv : G)
    (r₀ r₁ r₂ rv : ℕ)
    (hU₀ : U₀.index = 2 * r₀)
    (hU₁ : U₁.index = 4 * r₁)
    (hU₂ : U₂.index = 4 * r₂)
    (hV : V.index = 4 * rv)
    (hodd : r₀ % 2 = 1)
    (h01 : Nat.Coprime r₀ r₁) (h02 : Nat.Coprime r₀ r₂)
    (h0v : Nat.Coprime r₀ rv) (h12 : Nat.Coprime r₁ r₂)
    (h1v : Nat.Coprime r₁ rv) (h2v : Nat.Coprime r₂ rv)
    (hrel₁ : U₁.relIndex V = r₁)
    (hrel₂ : U₂.relIndex V = r₂)
    (hharmonic : IsHarmonicCosetFamily
      ![g₀, g₁, g₂, gv] ![U₀, U₁, U₂, V]) : False := by
  classical
  have hd01 := hharmonic (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  have hd02 := hharmonic (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd0v := hharmonic (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd12 := hharmonic (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd1v := hharmonic (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd2v := hharmonic (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  simp at hd01 hd02 hd0v hd12 hd1v hd2v
  rcases mixedPairData U₀ V g₀ gv hU₀ hV hodd h0v
      (fun x hx ↦ hd0v x hx.1 hx.2) with
    ⟨hrel₀, hrelV₀, hhalf₀, hhalfV₀⟩
  have hr₁pos : 0 < 4 * r₁ := by
    have hfinite : U₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hU₁] at hfinite
    omega
  have hr₂pos : 0 < 4 * r₂ := by
    have hfinite : U₂.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hU₂] at hfinite
    omega
  have hrelV₁ : V.relIndex U₁ = rv := by
    simpa using reverseRelIndex_of_commonFactor U₁ V hU₁ hV hr₁pos
      (k := 1) (by simpa using hrel₁)
  have hrelV₂ : V.relIndex U₂ = rv := by
    simpa using reverseRelIndex_of_commonFactor U₂ V hU₂ hV hr₂pos
      (k := 1) (by simpa using hrel₂)
  have heq10 := alphaOneIntersection_mul_eq_low U₁ V U₀
    hU₁ hV hU₀ hodd h01 h0v hrel₁ hrel₀
  have heq20 := alphaOneIntersection_mul_eq_low U₂ V U₀
    hU₂ hV hU₀ hodd h02 h0v hrel₂ hrel₀
  have heq21 := alphaOneIntersection_mul_eq_high U₂ V U₁
    hU₂ hV hU₁ h12 h1v hrel₂ hrel₁
  have hsub01 : (V : Set G) * (U₀ : Set G) ⊆
      (U₁ : Set G) * (U₀ : Set G) := by
    intro x hx
    rw [← heq10] at hx
    rcases hx with ⟨t, ht, u, hu, rfl⟩
    exact ⟨t, ht.1, u, hu, rfl⟩
  have hsub02 : (V : Set G) * (U₀ : Set G) ⊆
      (U₂ : Set G) * (U₀ : Set G) := by
    intro x hx
    rw [← heq20] at hx
    rcases hx with ⟨t, ht, u, hu, rfl⟩
    exact ⟨t, ht.1, u, hu, rfl⟩
  have hsub12 : (V : Set G) * (U₁ : Set G) ⊆
      (U₂ : Set G) * (U₁ : Set G) := by
    intro x hx
    rw [← heq21] at hx
    rcases hx with ⟨t, ht, u, hu, rfl⟩
    exact ⟨t, ht.1, u, hu, rfl⟩
  let A₀ : Set G := g₀ • ((U₀ : Set G) * (V : Set G))
  let A₁ : Set G := g₁ • ((U₁ : Set G) * (V : Set G))
  let A₂ : Set G := g₂ • ((U₂ : Set G) * (V : Set G))
  have hdA01 : Disjoint A₀ A₁ :=
    p45_thickened_disjoint U₀ U₁ V g₀ g₁ gv
      (fun x hx ↦ hd01 x hx.1 hx.2)
      (fun x hx ↦ hd0v x hx.1 hx.2)
      (fun x hx ↦ hd1v x hx.1 hx.2) hsub01
  have hdA02 : Disjoint A₀ A₂ :=
    p45_thickened_disjoint U₀ U₂ V g₀ g₂ gv
      (fun x hx ↦ hd02 x hx.1 hx.2)
      (fun x hx ↦ hd0v x hx.1 hx.2)
      (fun x hx ↦ hd2v x hx.1 hx.2) hsub02
  have hdA12 : Disjoint A₁ A₂ :=
    p45_thickened_disjoint U₁ U₂ V g₁ g₂ gv
      (fun x hx ↦ hd12 x hx.1 hx.2)
      (fun x hx ↦ hd1v x hx.1 hx.2)
      (fun x hx ↦ hd2v x hx.1 hx.2) hsub12
  have hdUnion : Disjoint (A₀ ∪ A₁) A₂ :=
    Set.disjoint_union_left.2 ⟨hdA02, hdA12⟩
  have hquarter₁ :
      4 * Nat.card ((U₁ : Set G) * (V : Set G)) = Nat.card G := by
    simpa using commonFactor_mul_natCard_subgroup_mul_eq
      U₁ V (k := 1) hV (by simpa using hrelV₁)
  have hquarter₂ :
      4 * Nat.card ((U₂ : Set G) * (V : Set G)) = Nat.card G := by
    simpa using commonFactor_mul_natCard_subgroup_mul_eq
      U₂ V (k := 1) hV (by simpa using hrelV₂)
  have hsum : Nat.card G =
      Nat.card ((U₀ : Set G) * (V : Set G)) +
      Nat.card ((U₁ : Set G) * (V : Set G)) +
      Nat.card ((U₂ : Set G) * (V : Set G)) := by omega
  have hcardUnion : ((A₀ ∪ A₁) ∪ A₂).ncard = Nat.card G := by
    rw [Set.ncard_union_eq hdUnion, Set.ncard_union_eq hdA01]
    simp only [A₀, A₁, A₂, Set.ncard_smul_set]
    simpa only [Nat.card_coe_set_eq] using hsum.symm
  have hunion : (A₀ ∪ A₁) ∪ A₂ = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [hcardUnion]
    simp
  have hgv : gv ∈ (A₀ ∪ A₁) ∪ A₂ := by rw [hunion]; trivial
  rcases hgv with (hgv0 | hgv1) | hgv2
  · have hmem : g₀⁻¹ * gv ∈ (U₀ : Set G) * (V : Set G) := by
      change gv ∈ g₀ • ((U₀ : Set G) * (V : Set G)) at hgv0
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hgv0
      exact hgv0
    rcases leftCosets_intersect_of_inv_mul_mem_mul U₀ V g₀ gv hmem with ⟨x, hx⟩
    exact hd0v x hx.1 hx.2
  · have hmem : g₁⁻¹ * gv ∈ (U₁ : Set G) * (V : Set G) := by
      change gv ∈ g₁ • ((U₁ : Set G) * (V : Set G)) at hgv1
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hgv1
      exact hgv1
    rcases leftCosets_intersect_of_inv_mul_mem_mul U₁ V g₁ gv hmem with ⟨x, hx⟩
    exact hd1v x hx.1 hx.2
  · have hmem : g₂⁻¹ * gv ∈ (U₂ : Set G) * (V : Set G) := by
      change gv ∈ g₂ • ((U₂ : Set G) * (V : Set G)) at hgv2
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hgv2
      exact hgv2
    rcases leftCosets_intersect_of_inv_mul_mem_mul U₂ V g₂ gv hmem with ⟨x, hx⟩
    exact hd2v x hx.1 hx.2

/-- The remaining nonuniform multiplier pattern in Proposition 4.5: two
three-multipliers meeting at `A` and a one-multiplier on the opposite edge. -/
private theorem p45_three_three_one_impossible
    {G : Type u} [Group G] [Finite G]
    (A B C : Subgroup G) (gA gB gC : G)
    (r₀ rA rB rC : ℕ)
    (hA : A.index = 4 * rA) (hB : B.index = 4 * rB)
    (hC : C.index = 4 * rC)
    (h0B : Nat.Coprime r₀ rB)
    (hAB : Nat.Coprime rA rB) (hAC : Nat.Coprime rA rC)
    (hBC : Nat.Coprime rB rC)
    (hthree0 : 3 ∣ r₀)
    (hrelAB : A.relIndex B = rA * 3)
    (hrelAC : A.relIndex C = rA * 3)
    (hrelBC : B.relIndex C = rB)
    (hharmonic : IsHarmonicCosetFamily ![gA, gB, gC] ![A, B, C]) :
    False := by
  classical
  have hdAB := hharmonic (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  have hdAC := hharmonic (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  have hdBC := hharmonic (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  simp at hdAB hdAC hdBC
  have hApos : 0 < 4 * rA := by
    have hfinite : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hA] at hfinite
    omega
  have hBpos : 0 < 4 * rB := by
    have hfinite : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hB] at hfinite
    omega
  have hrelCA : C.relIndex A = rC * 3 :=
    reverseRelIndex_of_commonFactor A C hA hC hApos hrelAC
  have hrelCB : C.relIndex B = rC := by
    simpa using reverseRelIndex_of_commonFactor B C hB hC hBpos
      (k := 1) (by simpa using hrelBC)
  let T : Subgroup G := A ⊓ C
  have hTindex : T.index = 4 * (3 * rA * rC) := by
    calc
      T.index = A.relIndex C * C.index := by
        simpa [T, Subgroup.inf_relIndex_right] using
          (Subgroup.relIndex_mul_index (H := A ⊓ C) (K := C)
            inf_le_right).symm
      _ = (rA * 3) * (4 * rC) := by rw [hrelAC, hC]
      _ = 4 * (3 * rA * rC) := by ring
  have hthreeB : Nat.Coprime 3 rB :=
    Nat.Coprime.of_dvd hthree0 (dvd_refl rB) h0B
  have hcopBT : Nat.Coprime rB (3 * rA * rC) :=
    (hthreeB.symm.mul_right hAB.symm).mul_right hBC
  have hTfinite : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases exists_relIndex_eq_residual_mul T B (m := 4)
      (r := 3 * rA * rC) (s := rB) (by omega) hTindex hB
      hcopBT.symm hTfinite with ⟨k, hk, hkpos⟩
  have hnorm :
      4 * Nat.card ((B : Set G) * (T : Set G)) = k * Nat.card G :=
    commonFactor_mul_natCard_subgroup_mul_eq B T hTindex hk
  have hsubBA : (B : Set G) * (T : Set G) ⊆
      (B : Set G) * (A : Set G) :=
    product_subset_product_of_le_right B T A inf_le_left
  have hsubBC : (B : Set G) * (T : Set G) ⊆
      (B : Set G) * (C : Set G) :=
    product_subset_product_of_le_right B T C inf_le_right
  have hquarterBC :
      4 * Nat.card ((B : Set G) * (C : Set G)) = Nat.card G := by
    simpa using commonFactor_mul_natCard_subgroup_mul_eq
      B C (k := 1) hC (by simpa using hrelCB)
  have hcardle : Nat.card ((B : Set G) * (T : Set G)) ≤
      Nat.card ((B : Set G) * (C : Set G)) := by
    simpa only [Nat.card_coe_set_eq] using
      Set.ncard_le_ncard hsubBC (Set.toFinite _)
  have hkone : k = 1 := by
    have h4le := Nat.mul_le_mul_left 4 hcardle
    have hkGle : k * Nat.card G ≤ 1 * Nat.card G := by
      calc
        k * Nat.card G = 4 * Nat.card ((B : Set G) * (T : Set G)) := hnorm.symm
        _ ≤ 4 * Nat.card ((B : Set G) * (C : Set G)) := h4le
        _ = Nat.card G := hquarterBC
        _ = 1 * Nat.card G := by simp
    have hkle : k ≤ 1 := Nat.le_of_mul_le_mul_right hkGle Nat.card_pos
    omega
  have heqBC : (B : Set G) * (T : Set G) =
      (B : Set G) * (C : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hsubBC
    have hinnerQuarter :
        4 * Nat.card ((B : Set G) * (T : Set G)) = Nat.card G := by
      simpa [hkone] using hnorm
    simpa only [Nat.card_coe_set_eq] using (by omega :
      Nat.card ((B : Set G) * (C : Set G)) ≤
        Nat.card ((B : Set G) * (T : Set G)))
  have hBC_BA : (B : Set G) * (C : Set G) ⊆
      (B : Set G) * (A : Set G) := by
    rw [← heqBC]
    exact hsubBA
  have hCB_AB : (C : Set G) * (B : Set G) ⊆
      (A : Set G) * (B : Set G) :=
    subgroup_mul_right_subset_of_mul_left_subset B C A hBC_BA
  have hthreeAC :
      4 * Nat.card ((A : Set G) * (C : Set G)) = 3 * Nat.card G :=
    commonFactor_mul_natCard_subgroup_mul_eq A C hC hrelCA
  have hcover : Nat.card G ≤
      Nat.card ((B : Set G) * (C : Set G)) +
        Nat.card ((A : Set G) * (C : Set G)) := by omega
  exact not_harmonic_three_of_product_cover B A C gB gA gC
    (fun x hx ↦ hdAB x hx.2 hx.1)
    (fun x hx ↦ hdBC x hx.1 hx.2)
    (fun x hx ↦ hdAC x hx.1 hx.2)
    hCB_AB hcover

private theorem p45_three_products_intersection_half
    {G : Type u} [Group G] [Finite G]
    (U₂ U₃ U₄ : Subgroup G) (g₂ g₃ g₄ : G)
    (r₀ r₂ r₃ r₄ : ℕ)
    (hU₂ : U₂.index = 4 * r₂) (hU₃ : U₃.index = 4 * r₃)
    (hU₄ : U₄.index = 4 * r₄)
    (h02 : Nat.Coprime r₀ r₂)
    (h23 : Nat.Coprime r₂ r₃) (h24 : Nat.Coprime r₂ r₄)
    (h34 : Nat.Coprime r₃ r₄)
    (hthree0 : 3 ∣ r₀)
    (hrel23 : U₂.relIndex U₃ = r₂ * 3)
    (hrel24 : U₂.relIndex U₄ = r₂ * 3)
    (hrel34 : U₃.relIndex U₄ = r₃ * 3)
    (hharmonic : IsHarmonicCosetFamily ![g₂, g₃, g₄] ![U₂, U₃, U₄]) :
    2 * ((((U₂ : Set G) * (U₃ : Set G)) ∩
      ((U₂ : Set G) * (U₄ : Set G))).ncard) = Nat.card G := by
  classical
  have hd23 := hharmonic (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  have hd24 := hharmonic (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  have hd34 := hharmonic (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  simp at hd23 hd24 hd34
  have hU₂pos : 0 < 4 * r₂ := by
    have hfinite : U₂.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hU₂] at hfinite
    omega
  have hU₃pos : 0 < 4 * r₃ := by
    have hfinite : U₃.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hU₃] at hfinite
    omega
  have hrel32 : U₃.relIndex U₂ = r₃ * 3 :=
    reverseRelIndex_of_commonFactor U₂ U₃ hU₂ hU₃ hU₂pos hrel23
  have hrel42 : U₄.relIndex U₂ = r₄ * 3 :=
    reverseRelIndex_of_commonFactor U₂ U₄ hU₂ hU₄ hU₂pos hrel24
  have hrel43 : U₄.relIndex U₃ = r₄ * 3 :=
    reverseRelIndex_of_commonFactor U₃ U₄ hU₃ hU₄ hU₃pos hrel34
  let B : Set G := (U₂ : Set G) * (U₃ : Set G)
  let C : Set G := (U₂ : Set G) * (U₄ : Set G)
  let X : Set G := B ∩ C
  have hthreeB : 4 * B.ncard = 3 * Nat.card G := by
    simpa only [B, Nat.card_coe_set_eq] using
      commonFactor_mul_natCard_subgroup_mul_eq U₂ U₃ hU₃ hrel32
  have hthreeC : 4 * C.ncard = 3 * Nat.card G := by
    simpa only [C, Nat.card_coe_set_eq] using
      commonFactor_mul_natCard_subgroup_mul_eq U₂ U₄ hU₄ hrel42
  have hthree43 :
      4 * Nat.card ((U₄ : Set G) * (U₃ : Set G)) = 3 * Nat.card G :=
    commonFactor_mul_natCard_subgroup_mul_eq U₄ U₃ hU₃ hrel34
  have hnoSubset : ¬B ⊆ C := by
    intro hBC
    have hinv : (U₃ : Set G) * (U₂ : Set G) ⊆
        (U₄ : Set G) * (U₂ : Set G) := by
      exact subgroup_mul_right_subset_of_mul_left_subset U₂ U₃ U₄ hBC
    have hcover : Nat.card G ≤
        Nat.card ((U₂ : Set G) * (U₃ : Set G)) +
          Nat.card ((U₄ : Set G) * (U₃ : Set G)) := by
      have hthreeBcard :
          4 * Nat.card ((U₂ : Set G) * (U₃ : Set G)) = 3 * Nat.card G := by
        simpa only [B, Nat.card_coe_set_eq] using hthreeB
      omega
    exact not_harmonic_three_of_product_cover U₂ U₄ U₃ g₂ g₄ g₃
      (fun x hx ↦ hd24 x hx.1 hx.2)
      (fun x hx ↦ hd23 x hx.1 hx.2)
      (fun x hx ↦ hd34 x hx.2 hx.1)
      hinv hcover
  let T : Subgroup G := U₃ ⊓ U₄
  have hTindex : T.index = 4 * (3 * r₃ * r₄) := by
    calc
      T.index = U₃.relIndex U₄ * U₄.index := by
        simpa [T, Subgroup.inf_relIndex_right] using
          (Subgroup.relIndex_mul_index (H := U₃ ⊓ U₄) (K := U₄)
            inf_le_right).symm
      _ = (r₃ * 3) * (4 * r₄) := by rw [hrel34, hU₄]
      _ = 4 * (3 * r₃ * r₄) := by ring
  have hthree2 : Nat.Coprime 3 r₂ :=
    Nat.Coprime.of_dvd hthree0 (dvd_refl r₂) h02
  have hcop2T : Nat.Coprime r₂ (3 * r₃ * r₄) :=
    (hthree2.symm.mul_right h23).mul_right h24
  have hTfinite : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases exists_relIndex_eq_residual_mul T U₂ (m := 4)
      (r := 3 * r₃ * r₄) (s := r₂) (by omega) hTindex hU₂
      hcop2T.symm hTfinite with ⟨k, hk, hkpos⟩
  let I : Set G := (U₂ : Set G) * (T : Set G)
  have hnormI : 4 * I.ncard = k * Nat.card G := by
    simpa only [I, Nat.card_coe_set_eq] using
      commonFactor_mul_natCard_subgroup_mul_eq U₂ T hTindex hk
  have hIB : I ⊆ B := by
    exact product_subset_product_of_le_right U₂ T U₃ inf_le_left
  have hIC : I ⊆ C := by
    exact product_subset_product_of_le_right U₂ T U₄ inf_le_right
  have hIX : I ⊆ X := fun x hx ↦ ⟨hIB hx, hIC hx⟩
  have hXlower : Nat.card G ≤ 2 * X.ncard := by
    have hunionLe : (B ∪ C).ncard ≤ Nat.card G := by
      simpa using Set.ncard_le_ncard (Set.subset_univ _) (Set.finite_univ)
    have hsum := Set.ncard_union_add_ncard_inter B C
    change (B ∪ C).ncard + X.ncard = B.ncard + C.ncard at hsum
    omega
  have hk_le_three : k ≤ 3 := by
    have hcardle : I.ncard ≤ B.ncard :=
      Set.ncard_le_ncard hIB (Set.toFinite _)
    have h4le := Nat.mul_le_mul_left 4 hcardle
    have hkGle : k * Nat.card G ≤ 3 * Nat.card G := by
      calc
        k * Nat.card G = 4 * I.ncard := hnormI.symm
        _ ≤ 4 * B.ncard := h4le
        _ = 3 * Nat.card G := hthreeB
    exact Nat.le_of_mul_le_mul_right hkGle Nat.card_pos
  have hdoubleSubset (x : G) (hx : x ∈ X) :
      DoubleCoset.doubleCoset x U₂ T ⊆ X := by
    exact doubleCoset_subset_inter_products U₂ U₃ U₄ x hx.1 hx.2
  have hdoubleDisjoint {x y : G}
      (hy : y ∉ DoubleCoset.doubleCoset x U₂ T) :
      Disjoint (DoubleCoset.doubleCoset x U₂ T)
        (DoubleCoset.doubleCoset y U₂ T) := by
    by_contra hnot
    have heq := DoubleCoset.eq_of_not_disjoint hnot
    apply hy
    rw [heq]
    exact DoubleCoset.mem_doubleCoset_self U₂ T y
  have hIeq : DoubleCoset.doubleCoset 1 U₂ T = I := by
    simp [I, DoubleCoset.doubleCoset]
  have hnoOutsideMakesCover (J : Set G) (hJX : J ⊆ X)
      (hIJ : Disjoint I J)
      (hlarge : 3 * Nat.card G ≤ 4 * (I ∪ J).ncard) : False := by
    have hUnionB : I ∪ J ⊆ B :=
      Set.union_subset hIB (hJX.trans Set.inter_subset_left)
    have hcardle := Set.ncard_le_ncard hUnionB (Set.toFinite _)
    have heqB : I ∪ J = B := by
      apply Set.eq_of_subset_of_ncard_le hUnionB
      have hle : B.ncard ≤ (I ∪ J).ncard := by omega
      exact hle
    apply hnoSubset
    rw [← heqB]
    exact Set.union_subset hIC (hJX.trans Set.inter_subset_right)
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with hk1 | hk2 | hk3
  · subst k
    have hnormI' : 4 * I.ncard = Nat.card G := by
      simpa using hnormI
    have hnotXsubI : ¬X ⊆ I := by
      intro hXI
      have hXeq : X = I := Set.Subset.antisymm hXI hIX
      rw [hXeq] at hXlower
      have hgpos : 0 < Nat.card G := Nat.card_pos
      omega
    rcases Set.not_subset.mp hnotXsubI with ⟨x, hxX, hxI⟩
    let D : Set G := DoubleCoset.doubleCoset x U₂ T
    have hDX : D ⊆ X := hdoubleSubset x hxX
    have hID : Disjoint I D := by
      rw [← hIeq]
      exact hdoubleDisjoint (by simpa [D, hIeq] using hxI)
    rcases exists_commonFactor_mul_ncard_doubleCoset_eq
        U₂ T x (m := 4) (r := r₂) (s := 3 * r₃ * r₄)
        (by omega) hU₂ hTindex hcop2T with ⟨l, hlpos, hnormD⟩
    have hnormD' : 4 * D.ncard = l * Nat.card G := by
      simpa [D] using hnormD
    have hlone : l = 1 := by
      have hUnionB : I ∪ D ⊆ B :=
        Set.union_subset hIB (hDX.trans Set.inter_subset_left)
      have hcardle := Set.ncard_le_ncard hUnionB (Set.toFinite _)
      have hcardUnion : (I ∪ D).ncard = I.ncard + D.ncard :=
        Set.ncard_union_eq hID
      have hlle : l ≤ 2 := by
        have h4le := Nat.mul_le_mul_left 4 hcardle
        rw [hcardUnion] at h4le
        have hsumEq : (1 + l) * Nat.card G =
            4 * (I.ncard + D.ncard) := by
          calc
            (1 + l) * Nat.card G = Nat.card G + l * Nat.card G := by ring
            _ = 4 * I.ncard + 4 * D.ncard := by rw [hnormI', hnormD']
            _ = 4 * (I.ncard + D.ncard) := by ring
        have hprodLe : (1 + l) * Nat.card G ≤ 3 * Nat.card G := by
          rw [hsumEq]
          exact h4le.trans_eq hthreeB
        have honePlus : 1 + l ≤ 3 :=
          Nat.le_of_mul_le_mul_right hprodLe Nat.card_pos
        omega
      rcases (by omega : l = 1 ∨ l = 2) with hl1 | hl2
      · exact hl1
      · subst l
        have hnormD'' : 4 * D.ncard = 2 * Nat.card G := by
          simpa using hnormD'
        exact (hnoOutsideMakesCover D hDX hID (by
          rw [Set.ncard_union_eq hID]
          omega)).elim
    subst l
    have hnormD'' : 4 * D.ncard = Nat.card G := by
      simpa using hnormD'
    have hXIunion : X ⊆ I ∪ D := by
      intro y hyX
      by_contra hynot
      have hyI : y ∉ I := fun h ↦ hynot (Or.inl h)
      have hyD : y ∉ D := fun h ↦ hynot (Or.inr h)
      let E : Set G := DoubleCoset.doubleCoset y U₂ T
      have hEX : E ⊆ X := hdoubleSubset y hyX
      have hIE : Disjoint I E := by
        rw [← hIeq]
        exact hdoubleDisjoint (by simpa [E, hIeq] using hyI)
      have hDE : Disjoint D E := hdoubleDisjoint (by simpa [D, E] using hyD)
      rcases exists_commonFactor_mul_ncard_doubleCoset_eq
          U₂ T y (m := 4) (r := r₂) (s := 3 * r₃ * r₄)
          (by omega) hU₂ hTindex hcop2T with ⟨e, hepos, hnormE⟩
      have hnormE' : 4 * E.ncard = e * Nat.card G := by
        simpa [E] using hnormE
      have hElower : Nat.card G ≤ 4 * E.ncard := by
        calc
          Nat.card G = 1 * Nat.card G := by simp
          _ ≤ e * Nat.card G := Nat.mul_le_mul_right _ hepos
          _ = 4 * E.ncard := hnormE'.symm
      have hdisjUnion : Disjoint (I ∪ D) E :=
        Set.disjoint_union_left.2 ⟨hIE, hDE⟩
      have hJX : (I ∪ D) ∪ E ⊆ X :=
        Set.union_subset (Set.union_subset hIX hDX) hEX
      have hlarge : 3 * Nat.card G ≤ 4 * ((I ∪ D) ∪ E).ncard := by
        rw [Set.ncard_union_eq hdisjUnion, Set.ncard_union_eq hID]
        omega
      have hIDE : Disjoint I (D ∪ E) :=
        Set.disjoint_union_right.2 ⟨hID, hIE⟩
      have hDEcard : (D ∪ E).ncard = D.ncard + E.ncard :=
        Set.ncard_union_eq hDE
      exact hnoOutsideMakesCover (D ∪ E)
        (Set.union_subset hDX hEX)
        hIDE
        (by
          simpa [Set.union_assoc] using hlarge)
    have hXeq : X = I ∪ D :=
      Set.Subset.antisymm hXIunion (Set.union_subset hIX hDX)
    change 2 * X.ncard = Nat.card G
    rw [hXeq, Set.ncard_union_eq hID]
    omega
  · subst k
    have hnormI' : 4 * I.ncard = 2 * Nat.card G := by
      simpa using hnormI
    have hXsubI : X ⊆ I := by
      intro x hxX
      by_contra hxI
      let D : Set G := DoubleCoset.doubleCoset x U₂ T
      have hDX : D ⊆ X := hdoubleSubset x hxX
      have hID : Disjoint I D := by
        rw [← hIeq]
        exact hdoubleDisjoint (by simpa [D, hIeq] using hxI)
      rcases exists_commonFactor_mul_ncard_doubleCoset_eq
          U₂ T x (m := 4) (r := r₂) (s := 3 * r₃ * r₄)
          (by omega) hU₂ hTindex hcop2T with ⟨l, hlpos, hnormD⟩
      have hnormD' : 4 * D.ncard = l * Nat.card G := by
        simpa [D] using hnormD
      have hDlower : Nat.card G ≤ 4 * D.ncard := by
        calc
          Nat.card G = 1 * Nat.card G := by simp
          _ ≤ l * Nat.card G := Nat.mul_le_mul_right _ hlpos
          _ = 4 * D.ncard := hnormD'.symm
      exact hnoOutsideMakesCover D hDX hID (by
        rw [Set.ncard_union_eq hID]
        omega)
    have hXeq : X = I := Set.Subset.antisymm hXsubI hIX
    change 2 * X.ncard = Nat.card G
    rw [hXeq]
    omega
  · subst k
    have hnormI' : 4 * I.ncard = 3 * Nat.card G := by
      simpa using hnormI
    have hIBEq : I = B := by
      apply Set.eq_of_subset_of_ncard_le hIB
      have hle : B.ncard ≤ I.ncard := by omega
      exact hle
    exfalso
    apply hnoSubset
    rw [← hIBEq]
    exact hIC

/-- The cardinality form of Lemma 3.1 used in the final case of
Proposition 4.5.  A half-set and two three-quarter-sets with the indicated
pairwise intersections cannot have a common point. -/
private theorem p45_triple_inter_eq_empty
    {α : Type u} [Finite α] (A B C : Set α)
    (hA : 2 * A.ncard = Nat.card α)
    (hB : 4 * B.ncard = 3 * Nat.card α)
    (hC : 4 * C.ncard = 3 * Nat.card α)
    (hAB : 4 * (A ∩ B).ncard = Nat.card α)
    (hAC : 4 * (A ∩ C).ncard = Nat.card α)
    (hBC : 2 * (B ∩ C).ncard = Nat.card α) :
    A ∩ B ∩ C = ∅ := by
  have hABsum := Set.ncard_union_add_ncard_inter A B
  have hACsum := Set.ncard_union_add_ncard_inter A C
  have hBCsum := Set.ncard_union_add_ncard_inter B C
  have hABcard : (A ∪ B).ncard = Nat.card α := by omega
  have hACcard : (A ∪ C).ncard = Nat.card α := by omega
  have hBCcard : (B ∪ C).ncard = Nat.card α := by omega
  have hABcover : A ∪ B = Set.univ :=
    (Set.eq_univ_iff_ncard (A ∪ B)).mpr hABcard
  have hACcover : A ∪ C = Set.univ :=
    (Set.eq_univ_iff_ncard (A ∪ C)).mpr hACcard
  have hBCcover : B ∪ C = Set.univ :=
    (Set.eq_univ_iff_ncard (B ∪ C)).mpr hBCcard
  have hAc := Set.ncard_add_ncard_compl A
  have hBc := Set.ncard_add_ncard_compl B
  have hCc := Set.ncard_add_ncard_compl C
  have hAcomp : 2 * Aᶜ.ncard = Nat.card α := by omega
  have hBcomp : 4 * Bᶜ.ncard = Nat.card α := by omega
  have hCcomp : 4 * Cᶜ.ncard = Nat.card α := by omega
  have hdAB : Disjoint Aᶜ Bᶜ := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hx : x ∈ A ∪ B := by rw [hABcover]; trivial
    rcases hx with hx | hx
    · exact hxA hx
    · exact hxB hx
  have hdAC : Disjoint Aᶜ Cᶜ := by
    rw [Set.disjoint_left]
    intro x hxA hxC
    have hx : x ∈ A ∪ C := by rw [hACcover]; trivial
    rcases hx with hx | hx
    · exact hxA hx
    · exact hxC hx
  have hdBC : Disjoint Bᶜ Cᶜ := by
    rw [Set.disjoint_left]
    intro x hxB hxC
    have hx : x ∈ B ∪ C := by rw [hBCcover]; trivial
    rcases hx with hx | hx
    · exact hxB hx
    · exact hxC hx
  have hdUnion : Disjoint (Aᶜ ∪ Bᶜ) Cᶜ :=
    Set.disjoint_union_left.2 ⟨hdAC, hdBC⟩
  have hCompUnionCard : ((Aᶜ ∪ Bᶜ) ∪ Cᶜ).ncard = Nat.card α := by
    rw [Set.ncard_union_eq hdUnion, Set.ncard_union_eq hdAB]
    omega
  have hCover : (Aᶜ ∪ Bᶜ) ∪ Cᶜ = Set.univ :=
    (Set.eq_univ_iff_ncard ((Aᶜ ∪ Bᶜ) ∪ Cᶜ)).mpr hCompUnionCard
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxComp : x ∈ (Aᶜ ∪ Bᶜ) ∪ Cᶜ := by rw [hCover]; trivial
  rcases hxComp with (hxA | hxB) | hxC
  · exact hxA hx.1.1
  · exact hxB hx.1.2
  · exact hxC hx.2

/-- Margolis--Schnabel Proposition 4.5 for finite groups.

A harmonic four-family cannot have one index `2 * r 0` and three indices
`4 * r i`, with the first residual odd and all four residuals pairwise
coprime. -/
theorem margolisSchnabel_prop4_5_finite
    {G : Type u} [Group G] [Finite G]
    (g : Fin 4 → G) (U : Fin 4 → Subgroup G) (r : Fin 4 → ℕ)
    (hindex0 : (U 0).index = 2 * r 0)
    (hindexHigh : ∀ i, i ≠ 0 → (U i).index = 4 * r i)
    (hodd : r 0 % 2 = 1)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j)) :
    ¬ IsHarmonicCosetFamily g U := by
  intro hharmonic
  let g₀ := g (0 : Fin 4)
  let g₁ := g (1 : Fin 4)
  let g₂ := g (2 : Fin 4)
  let g₃ := g (3 : Fin 4)
  let U₀ := U (0 : Fin 4)
  let U₁ := U (1 : Fin 4)
  let U₂ := U (2 : Fin 4)
  let U₃ := U (3 : Fin 4)
  let r₀ := r (0 : Fin 4)
  let r₁ := r (1 : Fin 4)
  let r₂ := r (2 : Fin 4)
  let r₃ := r (3 : Fin 4)
  have hU₀ : U₀.index = 2 * r₀ := by
    simpa [U₀, r₀] using hindex0
  have hU₁ : U₁.index = 4 * r₁ := by
    simpa [U₁, r₁] using hindexHigh 1 (by decide)
  have hU₂ : U₂.index = 4 * r₂ := by
    simpa [U₂, r₂] using hindexHigh 2 (by decide)
  have hU₃ : U₃.index = 4 * r₃ := by
    simpa [U₃, r₃] using hindexHigh 3 (by decide)
  have hodd₀ : r₀ % 2 = 1 := by simpa [r₀] using hodd
  have hc01 : Nat.Coprime r₀ r₁ := by
    simpa [r₀, r₁] using hcop 0 1 (by decide)
  have hc02 : Nat.Coprime r₀ r₂ := by
    simpa [r₀, r₂] using hcop 0 2 (by decide)
  have hc03 : Nat.Coprime r₀ r₃ := by
    simpa [r₀, r₃] using hcop 0 3 (by decide)
  have hc12 : Nat.Coprime r₁ r₂ := by
    simpa [r₁, r₂] using hcop 1 2 (by decide)
  have hc13 : Nat.Coprime r₁ r₃ := by
    simpa [r₁, r₃] using hcop 1 3 (by decide)
  have hc23 : Nat.Coprime r₂ r₃ := by
    simpa [r₂, r₃] using hcop 2 3 (by decide)
  have hhFull : IsHarmonicCosetFamily
      ![g₀, g₁, g₂, g₃] ![U₀, U₁, U₂, U₃] := by
    convert hharmonic using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh012 : IsHarmonicCosetFamily
      ![g₀, g₁, g₂] ![U₀, U₁, U₂] := by
    let e : Fin 3 ↪ Fin 4 := ⟨![0, 1, 2], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh013 : IsHarmonicCosetFamily
      ![g₀, g₁, g₃] ![U₀, U₁, U₃] := by
    let e : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh023 : IsHarmonicCosetFamily
      ![g₀, g₂, g₃] ![U₀, U₂, U₃] := by
    let e : Fin 3 ↪ Fin 4 := ⟨![0, 2, 3], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh123 : IsHarmonicCosetFamily
      ![g₁, g₂, g₃] ![U₁, U₂, U₃] := by
    let e : Fin 3 ↪ Fin 4 := ⟨![1, 2, 3], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh0132 : IsHarmonicCosetFamily
      ![g₀, g₁, g₃, g₂] ![U₀, U₁, U₃, U₂] := by
    let e : Fin 4 ↪ Fin 4 := ⟨![0, 1, 3, 2], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh0231 : IsHarmonicCosetFamily
      ![g₀, g₂, g₃, g₁] ![U₀, U₂, U₃, U₁] := by
    let e : Fin 4 ↪ Fin 4 := ⟨![0, 2, 3, 1], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh213 : IsHarmonicCosetFamily
      ![g₂, g₁, g₃] ![U₂, U₁, U₃] := by
    let e : Fin 3 ↪ Fin 4 := ⟨![2, 1, 3], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hh312 : IsHarmonicCosetFamily
      ![g₃, g₁, g₂] ![U₃, U₁, U₂] := by
    let e : Fin 3 ↪ Fin 4 := ⟨![3, 1, 2], by decide⟩
    convert hharmonic.comp e using 1 <;> funext i <;> fin_cases i <;> rfl
  have hd01 := hhFull (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  have hd02 := hhFull (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd03 := hhFull (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd12 := hhFull (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd13 := hhFull (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd23 := hhFull (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  simp at hd01 hd02 hd03 hd12 hd13 hd23
  have hL012 := margolisSchnabelLemma44 U₀ U₁ U₂ g₀ g₁ g₂
    r₀ r₁ r₂ hU₀ hU₁ hU₂ hodd₀ hc01 hc02 hc12 hh012
  have hL013 := margolisSchnabelLemma44 U₀ U₁ U₃ g₀ g₁ g₃
    r₀ r₁ r₃ hU₀ hU₁ hU₃ hodd₀ hc01 hc03 hc13 hh013
  have hL023 := margolisSchnabelLemma44 U₀ U₂ U₃ g₀ g₂ g₃
    r₀ r₂ r₃ hU₀ hU₂ hU₃ hodd₀ hc02 hc03 hc23 hh023
  rcases fourPairMultiplier U₁ U₂ g₁ g₂ hU₁ hU₂ hc12
      (fun x hx ↦ hd12 x hx.1 hx.2) with
    ⟨k12, hk12cases, hrel12, hrel21, hcard12⟩
  rcases fourPairMultiplier U₁ U₃ g₁ g₃ hU₁ hU₃ hc13
      (fun x hx ↦ hd13 x hx.1 hx.2) with
    ⟨k13, hk13cases, hrel13, hrel31, hcard13⟩
  rcases fourPairMultiplier U₂ U₃ g₂ g₃ hU₂ hU₃ hc23
      (fun x hx ↦ hd23 x hx.1 hx.2) with
    ⟨k23, hk23cases, hrel23, hrel32, hcard23⟩
  have hk12 : k12 = 1 ∨ k12 = 3 := by
    rcases hk12cases with hk | hk | hk
    · exact Or.inl hk
    · exfalso
      apply hL012.1
      simpa [hk] using hrel12
    · exact Or.inr hk
  have hk13 : k13 = 1 ∨ k13 = 3 := by
    rcases hk13cases with hk | hk | hk
    · exact Or.inl hk
    · exfalso
      apply hL013.1
      simpa [hk] using hrel13
    · exact Or.inr hk
  have hk23 : k23 = 1 ∨ k23 = 3 := by
    rcases hk23cases with hk | hk | hk
    · exact Or.inl hk
    · exfalso
      apply hL023.1
      simpa [hk] using hrel23
    · exact Or.inr hk
  rcases hk12 with hk12 | hk12
  · rcases hk13 with hk13 | hk13
    · rcases hk23 with hk23 | hk23
      · have hrel13' : U₁.relIndex U₃ = r₁ := by
          simpa [hk13] using hrel13
        have hrel23' : U₂.relIndex U₃ = r₂ := by
          simpa [hk23] using hrel23
        exact p45_proposition38_mixed_anchor U₀ U₁ U₂ U₃
          g₀ g₁ g₂ g₃ r₀ r₁ r₂ r₃ hU₀ hU₁ hU₂ hU₃ hodd₀
          hc01 hc02 hc03 hc12 hc13 hc23 hrel13' hrel23' hhFull
      · have hrel21' : U₂.relIndex U₁ = r₂ := by
          simpa [hk12] using hrel21
        have hrel31' : U₃.relIndex U₁ = r₃ := by
          simpa [hk13] using hrel31
        exact p45_proposition38_mixed_anchor U₀ U₂ U₃ U₁
          g₀ g₂ g₃ g₁ r₀ r₂ r₃ r₁ hU₀ hU₂ hU₃ hU₁ hodd₀
          hc02 hc03 hc01 hc23 hc12.symm hc13.symm hrel21' hrel31' hh0231
    · rcases hk23 with hk23 | hk23
      · have hrel12' : U₁.relIndex U₂ = r₁ := by
          simpa [hk12] using hrel12
        have hrel32' : U₃.relIndex U₂ = r₃ := by
          simpa [hk23] using hrel32
        exact p45_proposition38_mixed_anchor U₀ U₁ U₃ U₂
          g₀ g₁ g₃ g₂ r₀ r₁ r₃ r₂ hU₀ hU₁ hU₃ hU₂ hodd₀
          hc01 hc03 hc02 hc13 hc12 hc23.symm hrel12' hrel32' hh0132
      · have hrel31' : U₃.relIndex U₁ = r₃ * 3 := by
          simpa [hk13] using hrel31
        have hrel32' : U₃.relIndex U₂ = r₃ * 3 := by
          simpa [hk23] using hrel32
        have hrel12' : U₁.relIndex U₂ = r₁ := by
          simpa [hk12] using hrel12
        have hthree0 : 3 ∣ r₀ :=
          (hL013.2 (by simpa [hk13] using hrel13)).1
        exact p45_three_three_one_impossible U₃ U₁ U₂ g₃ g₁ g₂
          r₀ r₃ r₁ r₂ hU₃ hU₁ hU₂ hc01 hc13.symm hc23.symm hc12
          hthree0 hrel31' hrel32' hrel12' hh312
  · rcases hk13 with hk13 | hk13
    · rcases hk23 with hk23 | hk23
      · have hrel13' : U₁.relIndex U₃ = r₁ := by
          simpa [hk13] using hrel13
        have hrel23' : U₂.relIndex U₃ = r₂ := by
          simpa [hk23] using hrel23
        exact p45_proposition38_mixed_anchor U₀ U₁ U₂ U₃
          g₀ g₁ g₂ g₃ r₀ r₁ r₂ r₃ hU₀ hU₁ hU₂ hU₃ hodd₀
          hc01 hc02 hc03 hc12 hc13 hc23 hrel13' hrel23' hhFull
      · have hrel21' : U₂.relIndex U₁ = r₂ * 3 := by
          simpa [hk12] using hrel21
        have hrel23' : U₂.relIndex U₃ = r₂ * 3 := by
          simpa [hk23] using hrel23
        have hrel13' : U₁.relIndex U₃ = r₁ := by
          simpa [hk13] using hrel13
        have hthree0 : 3 ∣ r₀ :=
          (hL012.2 (by simpa [hk12] using hrel12)).1
        exact p45_three_three_one_impossible U₂ U₁ U₃ g₂ g₁ g₃
          r₀ r₂ r₁ r₃ hU₂ hU₁ hU₃ hc01 hc12.symm hc23 hc13
          hthree0 hrel21' hrel23' hrel13' hh213
    · rcases hk23 with hk23 | hk23
      · have hrel12' : U₁.relIndex U₂ = r₁ * 3 := by
          simpa [hk12] using hrel12
        have hrel13' : U₁.relIndex U₃ = r₁ * 3 := by
          simpa [hk13] using hrel13
        have hrel23' : U₂.relIndex U₃ = r₂ := by
          simpa [hk23] using hrel23
        have hthree0 : 3 ∣ r₀ := (hL012.2 hrel12').1
        exact p45_three_three_one_impossible U₁ U₂ U₃ g₁ g₂ g₃
          r₀ r₁ r₂ r₃ hU₁ hU₂ hU₃ hc02 hc12 hc13 hc23
          hthree0 hrel12' hrel13' hrel23' hh123
      · have hrel12' : U₁.relIndex U₂ = r₁ * 3 := by
          simpa [hk12] using hrel12
        have hrel13' : U₁.relIndex U₃ = r₁ * 3 := by
          simpa [hk13] using hrel13
        have hrel23' : U₂.relIndex U₃ = r₂ * 3 := by
          simpa [hk23] using hrel23
        have hL12 := hL012.2 hrel12'
        have hL13 := hL013.2 hrel13'
        have hhalfBC := p45_three_products_intersection_half
          U₁ U₂ U₃ g₁ g₂ g₃ r₀ r₁ r₂ r₃ hU₁ hU₂ hU₃
          hc01 hc12 hc13 hc23 hL12.1 hrel12' hrel13' hrel23' hh123
        rcases mixedPairData U₀ U₁ g₀ g₁ hU₀ hU₁ hodd₀ hc01
            (fun x hx ↦ hd01 x hx.1 hx.2) with
          ⟨hrel01, hrel10, hhalf01, hhalf10⟩
        let A : Set G := (U₁ : Set G) * (U₀ : Set G)
        let B : Set G := (U₁ : Set G) * (U₂ : Set G)
        let C : Set G := (U₁ : Set G) * (U₃ : Set G)
        have hA : 2 * A.ncard = Nat.card G := by
          simpa only [A, Nat.card_coe_set_eq] using hhalf10
        have hB : 4 * B.ncard = 3 * Nat.card G := by
          simpa only [B, Nat.card_coe_set_eq, hk12] using hcard12
        have hC : 4 * C.ncard = 3 * Nat.card G := by
          simpa only [C, Nat.card_coe_set_eq, hk13] using hcard13
        have hAB : 4 * (A ∩ B).ncard = Nat.card G := by
          simpa only [A, B] using hL12.2.2
        have hAC : 4 * (A ∩ C).ncard = Nat.card G := by
          simpa only [A, C] using hL13.2.2
        have hBC : 2 * (B ∩ C).ncard = Nat.card G := by
          simpa only [B, C] using hhalfBC
        have hEmpty := p45_triple_inter_eq_empty A B C
          hA hB hC hAB hAC hBC
        have hone : (1 : G) ∈ A ∩ B ∩ C := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · exact ⟨1, U₁.one_mem, 1, U₀.one_mem, by simp [A]⟩
          · exact ⟨1, U₁.one_mem, 1, U₂.one_mem, by simp [B]⟩
          · exact ⟨1, U₁.one_mem, 1, U₃.one_mem, by simp [C]⟩
        rw [hEmpty] at hone
        exact hone

end ErdosProblems.E274
