import ErdosProblems.E274.GroupFiberBasics
import Mathlib.GroupTheory.DoubleCoset

/-!
# Margolis--Schnabel Proposition 4.3

This file proves, for finite groups, Proposition 4.3 of Margolis--Schnabel:
four subgroup indices of the form `3 * r i`, with pairwise-coprime residuals,
cannot support four pairwise disjoint chosen left cosets.

The proof follows the source's intersection-multiplier argument.  The local
lemmas below use `relIndex` instead of introducing a separate `alpha`
definition: `U.relIndex V = r * alpha` is the same multiplier identity.
-/

namespace ErdosProblems.E274

open scoped Pointwise

universe u

/- The shared finite-harmonic module is developed in parallel.  These two
small source-level helpers are kept local to this file so Proposition 4.3 can
compile independently; they can later be replaced by the identically stated
shared lemmas. -/

private theorem p43_leftCosets_intersect_of_inv_mul_mem_mul
    {G : Type u} [Group G] (U V : Subgroup G) (a b : G)
    (hmem : a⁻¹ * b ∈ (U : Set G) * (V : Set G)) :
    ∃ x, InLeftCoset a U x ∧ InLeftCoset b V x := by
  rcases hmem with ⟨u, hu, v, hv, huv⟩
  have hvInv : v⁻¹ ∈ V := V.inv_mem hv
  refine ⟨b * v⁻¹, ?_, by simpa [InLeftCoset] using hvInv⟩
  have hba : b = a * (u * v) := by
    calc
      b = a * (a⁻¹ * b) := by simp
      _ = a * (u * v) := by rw [← huv]
  rw [hba]
  simpa [InLeftCoset, mul_assoc] using hu

private theorem p43_inv_mul_notMem_mul_of_disjoint_leftCosets
    {G : Type u} [Group G] (U V : Subgroup G) (a b : G)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    a⁻¹ * b ∉ (U : Set G) * (V : Set G) := by
  intro hmem
  rcases p43_leftCosets_intersect_of_inv_mul_mem_mul U V a b hmem with
    ⟨x, hx⟩
  exact hdisjoint x hx

private theorem p43_relIndex_lt_index_of_disjoint_leftCosets
    {G : Type u} [Group G] (U V : Subgroup G) (a b : G)
    (hU : U.index ≠ 0)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    U.relIndex V < U.index := by
  classical
  have hrel : U.relIndex V ≠ 0 := by
    intro hzero
    exact hU (U.index_eq_zero_of_relIndex_eq_zero hzero)
  letI : Fintype (G ⧸ U) := U.fintypeOfIndexNeZero hU
  letI : Fintype (V ⧸ U.subgroupOf V) :=
    (U.subgroupOf V).fintypeOfIndexNeZero hrel
  have hnonsurj :
      ¬Function.Surjective (shiftedCellBoxEmbedding U V b) := by
    intro hsurj
    rcases hsurj (QuotientGroup.mk a) with ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | _ v =>
        have hcellU : InLeftCoset a U (b * (v : G)) := by
          rw [InLeftCoset, ← QuotientGroup.eq]
          simpa using hq.symm
        have hcellV : InLeftCoset b V (b * (v : G)) := by
          simp [InLeftCoset]
        exact hdisjoint (b * (v : G)) ⟨hcellU, hcellV⟩
  have hcard := Fintype.card_lt_of_injective_not_surjective
    (shiftedCellBoxEmbedding U V b)
    (shiftedCellBoxEmbedding U V b).injective hnonsurj
  have hcardDom :
      Fintype.card (V ⧸ U.subgroupOf V) = U.relIndex V := by
    rw [← Nat.card_eq_fintype_card, ← (U.subgroupOf V).index_eq_card]
    rfl
  have hcardCod : Fintype.card (G ⧸ U) = U.index := by
    rw [← Nat.card_eq_fintype_card, ← U.index_eq_card]
  simpa only [hcardDom, hcardCod] using hcard

private theorem p43_natCard_subgroup_mul
    {G : Type u} [Group G] [Finite G] (U V : Subgroup G) :
    Nat.card ((U : Set G) * (V : Set G)) =
      Nat.card V * V.relIndex U := by
  classical
  let f := shiftedCellBoxEmbedding V U (1 : G)
  have hrange :
      Set.range f =
        (U : Set G).image (fun x : G ↦ (QuotientGroup.mk x : G ⧸ V)) := by
    ext q
    constructor
    · rintro ⟨qU, rfl⟩
      induction qU using QuotientGroup.induction_on with
      | _ u =>
          exact ⟨u, u.property, by simp [f]⟩
    · rintro ⟨x, hxU, rfl⟩
      refine ⟨QuotientGroup.mk ⟨x, hxU⟩, ?_⟩
      simp [f]
  have hcardRange : Nat.card (Set.range f) = V.relIndex U := by
    calc
      Nat.card (Set.range f) = Nat.card (U ⧸ V.subgroupOf U) :=
        Nat.card_congr (Equiv.ofInjective f f.injective).symm
      _ = V.relIndex U := by
        rw [← (V.subgroupOf U).index_eq_card]
        rfl
  have hcardImage :
      Nat.card ((U : Set G).image
        (fun x : G ↦ (QuotientGroup.mk x : G ⧸ V))) = V.relIndex U := by
    rw [← hrange]
    exact hcardRange
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient]
  exact congrArg (Nat.card V * ·) hcardImage

/-- Division-free form of the source identity
`|UV| = c |G| / 3`. -/
private theorem p43_three_mul_natCard_mul_eq
    {G : Type u} [Group G] [Finite G] (U V : Subgroup G)
    {s c : ℕ} (hV : V.index = 3 * s)
    (hrel : V.relIndex U = c * s) :
    3 * Nat.card ((U : Set G) * (V : Set G)) = c * Nat.card G := by
  rw [p43_natCard_subgroup_mul, hrel]
  have hcard := V.card_mul_index
  rw [hV] at hcard
  calc
    3 * (Nat.card V * (c * s)) = c * (Nat.card V * (3 * s)) := by ring
    _ = c * Nat.card G := by rw [hcard]

/-- The source's thickening claim in Lemma 3.5: under the displayed product
inclusion, two disjoint chosen cells remain disjoint after right thickening by
the anchor subgroup. -/
private theorem p43_thickened_disjoint
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
  have huinv : ui⁻¹ ∈ Ui := Ui.inv_mem hui
  have hsmall : (v' * v⁻¹) * ui⁻¹ ∈
      (V : Set G) * (Ui : Set G) :=
    ⟨v' * v⁻¹, hvpart, ui⁻¹, huinv, rfl⟩
  rcases hsubset hsmall with ⟨uj', huj', ui', hui', heqSmall⟩
  have hnot := p43_inv_mul_notMem_mul_of_disjoint_leftCosets Uj Ui gj gi
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

private theorem p43_reverse_relIndex_eq_of_thrice_indices
    {G : Type u} [Group G] (U V : Subgroup G)
    {r s c : ℕ} (hU : U.index = 3 * r) (hV : V.index = 3 * s)
    (hrpos : 0 < r) (hforward : U.relIndex V = c * r) :
    V.relIndex U = c * s := by
  have hinterU : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hinterV : V.relIndex U * U.index = (U ⊓ V).index := by
    rw [inf_comm]
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := V ⊓ U) (K := U) inf_le_right)
  have hmul : (3 * r) * (c * s) = (3 * r) * V.relIndex U := by
    calc
      (3 * r) * (c * s) = (c * r) * (3 * s) := by ring
      _ = (U ⊓ V).index := by rw [← hinterU, hforward, hV]
      _ = V.relIndex U * (3 * r) := by rw [← hinterV, hU]
      _ = (3 * r) * V.relIndex U := by ring
  exact (Nat.mul_left_cancel (by omega) hmul).symm

/-- Equality used in Proposition 3.8: if `Ui` and `Uj` both have source
multiplier one with the anchor `V`, then `(Ui ∩ V) Uj = V Uj`. -/
private theorem p43_inf_mul_eq_of_alpha_one
    {G : Type u} [Group G] [Finite G]
    (Ui V Uj : Subgroup G) {ri rv rj : ℕ}
    (hUi : Ui.index = 3 * ri) (hV : V.index = 3 * rv)
    (hUj : Uj.index = 3 * rj)
    (hiv : Nat.Coprime ri rv) (hij : Nat.Coprime ri rj)
    (hvj : Nat.Coprime rv rj)
    (hrelUiV : Ui.relIndex V = ri)
    (hrelUjV : Uj.relIndex V = rj) :
    ((Ui ⊓ V : Subgroup G) : Set G) * (Uj : Set G) =
      (V : Set G) * (Uj : Set G) := by
  have hrvpos : 0 < rv := by
    have hVfinite : V.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hrjpos : 0 < rj := by
    have hUjfinite : Uj.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    by_contra h
    have : rj = 0 := Nat.eq_zero_of_not_pos h
    exact hUjfinite (by simp [hUj, this])
  have hTindex : (Ui ⊓ V).index = 3 * (ri * rv) := by
    have h := Subgroup.relIndex_mul_index
      (H := Ui ⊓ V) (K := V) inf_le_right
    simp only [Subgroup.inf_relIndex_right] at h
    rw [hrelUiV, hV] at h
    nlinarith
  have hrelFinite : Uj.relIndex V ≠ 0 := by omega
  have hupper : Uj.relIndex (Ui ⊓ V) ≤ rj := by
    simpa [hrelUjV] using Subgroup.relIndex_le_of_le_right
      (H := Uj) (K := Ui ⊓ V) (L := V) inf_le_right hrelFinite
  have hdivIndex : Uj.index ∣ (Uj ⊓ (Ui ⊓ V)).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : Uj.relIndex (Ui ⊓ V) * (Ui ⊓ V).index =
      (Uj ⊓ (Ui ⊓ V)).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index
        (H := Uj ⊓ (Ui ⊓ V)) (K := Ui ⊓ V) inf_le_right)
  have hraw : 3 * rj ∣ Uj.relIndex (Ui ⊓ V) * (3 * (ri * rv)) := by
    rw [← hinter, hUj, hTindex] at hdivIndex
    exact hdivIndex
  have hcancel : rj ∣ Uj.relIndex (Ui ⊓ V) * (ri * rv) := by
    have : 3 * rj ∣ 3 * (Uj.relIndex (Ui ⊓ V) * (ri * rv)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
  have hcop : Nat.Coprime rj (ri * rv) :=
    (hij.symm.mul_right hvj.symm)
  have hdiv : rj ∣ Uj.relIndex (Ui ⊓ V) :=
    hcop.dvd_of_dvd_mul_right hcancel
  have hpositive : 0 < Uj.relIndex (Ui ⊓ V) := by
    have hne : Uj.relIndex (Ui ⊓ V) ≠ 0 := by
      intro hz
      exact hrelFinite
        (Subgroup.relIndex_eq_zero_of_le_right inf_le_right hz)
    exact Nat.pos_of_ne_zero hne
  rcases hdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    rw [hk] at hpositive
    nlinarith
  have hkle : k ≤ 1 := by
    rw [hk] at hupper
    nlinarith
  have hkone : k = 1 := by omega
  have hrel : Uj.relIndex (Ui ⊓ V) = rj := by
    simpa [hkone] using hk
  have hsubset : ((Ui ⊓ V : Subgroup G) : Set G) * (Uj : Set G) ⊆
      (V : Set G) * (Uj : Set G) := by
    rintro x ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht.2, y, hy, rfl⟩
  apply Set.eq_of_subset_of_ncard_le (s :=
      ((Ui ⊓ V : Subgroup G) : Set G) * (Uj : Set G))
    (t := (V : Set G) * (Uj : Set G)) hsubset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    p43_natCard_subgroup_mul, p43_natCard_subgroup_mul, hrel, hrelUjV]

/-- The `n = 3` case of source Proposition 3.8. -/
private theorem p43_proposition38_three
    {G : Type u} [Group G] [Finite G]
    (U₀ U₁ U₂ V : Subgroup G) (g₀ g₁ g₂ gv : G)
    {r₀ r₁ r₂ rv : ℕ}
    (hU₀ : U₀.index = 3 * r₀) (hU₁ : U₁.index = 3 * r₁)
    (hU₂ : U₂.index = 3 * r₂) (hV : V.index = 3 * rv)
    (h01 : Nat.Coprime r₀ r₁) (h02 : Nat.Coprime r₀ r₂)
    (h0v : Nat.Coprime r₀ rv) (h12 : Nat.Coprime r₁ r₂)
    (h1v : Nat.Coprime r₁ rv) (h2v : Nat.Coprime r₂ rv)
    (hrel₀ : U₀.relIndex V = r₀)
    (hrel₁ : U₁.relIndex V = r₁)
    (hrel₂ : U₂.relIndex V = r₂)
    (hharmonic : IsHarmonicCosetFamily
      ![g₀, g₁, g₂, gv] ![U₀, U₁, U₂, V]) : False := by
  have hd01 := hharmonic (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  have hd02 := hharmonic (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd0v := hharmonic (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd12 := hharmonic (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have hd1v := hharmonic (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hd2v := hharmonic (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  simp at hd01 hd02 hd0v hd12 hd1v hd2v
  have hrvpos : 0 < rv := by
    have hVfinite : V.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hrev₀ : V.relIndex U₀ = rv := by
    simpa using p43_reverse_relIndex_eq_of_thrice_indices U₀ V (c := 1) hU₀ hV
      (by
        have hUfinite : U₀.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
        by_contra h
        have : r₀ = 0 := Nat.eq_zero_of_not_pos h
        exact hUfinite (by simp [hU₀, this])) (by simpa using hrel₀)
  have hrev₁ : V.relIndex U₁ = rv := by
    simpa using p43_reverse_relIndex_eq_of_thrice_indices U₁ V (c := 1) hU₁ hV
      (by
        have hUfinite : U₁.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
        by_contra h
        have : r₁ = 0 := Nat.eq_zero_of_not_pos h
        exact hUfinite (by simp [hU₁, this])) (by simpa using hrel₁)
  have hrev₂ : V.relIndex U₂ = rv := by
    simpa using p43_reverse_relIndex_eq_of_thrice_indices U₂ V (c := 1) hU₂ hV
      (by
        have hUfinite : U₂.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
        by_contra h
        have : r₂ = 0 := Nat.eq_zero_of_not_pos h
        exact hUfinite (by simp [hU₂, this])) (by simpa using hrel₂)
  have heq01 := p43_inf_mul_eq_of_alpha_one U₀ V U₁
    hU₀ hV hU₁ h0v h01 h1v.symm hrel₀ hrel₁
  have heq02 := p43_inf_mul_eq_of_alpha_one U₀ V U₂
    hU₀ hV hU₂ h0v h02 h2v.symm hrel₀ hrel₂
  have heq12 := p43_inf_mul_eq_of_alpha_one U₁ V U₂
    hU₁ hV hU₂ h1v h12 h2v.symm hrel₁ hrel₂
  have hsub01 : (V : Set G) * (U₀ : Set G) ⊆
      (U₁ : Set G) * (U₀ : Set G) := by
    intro x hx
    have heq := p43_inf_mul_eq_of_alpha_one U₁ V U₀
      hU₁ hV hU₀ h1v h01.symm h0v.symm hrel₁ hrel₀
    rw [← heq] at hx
    rcases hx with ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht.1, y, hy, rfl⟩
  have hsub02 : (V : Set G) * (U₀ : Set G) ⊆
      (U₂ : Set G) * (U₀ : Set G) := by
    intro x hx
    have heq := p43_inf_mul_eq_of_alpha_one U₂ V U₀
      hU₂ hV hU₀ h2v h02.symm h0v.symm hrel₂ hrel₀
    rw [← heq] at hx
    rcases hx with ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht.1, y, hy, rfl⟩
  have hsub12 : (V : Set G) * (U₁ : Set G) ⊆
      (U₂ : Set G) * (U₁ : Set G) := by
    intro x hx
    have heq := p43_inf_mul_eq_of_alpha_one U₂ V U₁
      hU₂ hV hU₁ h2v h12.symm h1v.symm hrel₂ hrel₁
    rw [← heq] at hx
    rcases hx with ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht.1, y, hy, rfl⟩
  let A₀ : Set G := g₀ • ((U₀ : Set G) * (V : Set G))
  let A₁ : Set G := g₁ • ((U₁ : Set G) * (V : Set G))
  let A₂ : Set G := g₂ • ((U₂ : Set G) * (V : Set G))
  have hdA01 : Disjoint A₀ A₁ :=
    p43_thickened_disjoint U₀ U₁ V g₀ g₁ gv
      (fun x hx ↦ hd01 x hx.1 hx.2)
      (fun x hx ↦ hd0v x hx.1 hx.2)
      (fun x hx ↦ hd1v x hx.1 hx.2) hsub01
  have hdA02 : Disjoint A₀ A₂ :=
    p43_thickened_disjoint U₀ U₂ V g₀ g₂ gv
      (fun x hx ↦ hd02 x hx.1 hx.2)
      (fun x hx ↦ hd0v x hx.1 hx.2)
      (fun x hx ↦ hd2v x hx.1 hx.2) hsub02
  have hdA12 : Disjoint A₁ A₂ :=
    p43_thickened_disjoint U₁ U₂ V g₁ g₂ gv
      (fun x hx ↦ hd12 x hx.1 hx.2)
      (fun x hx ↦ hd1v x hx.1 hx.2)
      (fun x hx ↦ hd2v x hx.1 hx.2) hsub12
  have hdUnion : Disjoint (A₀ ∪ A₁) A₂ := by
    exact Set.disjoint_union_left.2 ⟨hdA02, hdA12⟩
  have hc₀ := p43_three_mul_natCard_mul_eq U₀ V (c := 1) hV
    (by simpa using hrev₀)
  have hc₁ := p43_three_mul_natCard_mul_eq U₁ V (c := 1) hV
    (by simpa using hrev₁)
  have hc₂ := p43_three_mul_natCard_mul_eq U₂ V (c := 1) hV
    (by simpa using hrev₂)
  have hsum : Nat.card G =
      Nat.card ((U₀ : Set G) * (V : Set G)) +
      Nat.card ((U₁ : Set G) * (V : Set G)) +
      Nat.card ((U₂ : Set G) * (V : Set G)) := by omega
  have hcardUnion : ((A₀ ∪ A₁) ∪ A₂).ncard = Nat.card G := by
    rw [Set.ncard_union_eq hdUnion, Set.ncard_union_eq hdA01]
    simp only [A₀, A₁, A₂, Set.ncard_smul_set]
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, ← hsum]
  have hunion : (A₀ ∪ A₁) ∪ A₂ = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (s := (A₀ ∪ A₁) ∪ A₂)
      (t := Set.univ) (by intro x hx; trivial)
    simpa [hcardUnion]
  have hgv : gv ∈ (A₀ ∪ A₁) ∪ A₂ := by rw [hunion]; trivial
  rcases hgv with (hgv | hgv) | hgv
  · rcases hgv with ⟨y, ⟨u, hu, v, hv, rfl⟩, hy⟩
    apply (p43_inv_mul_notMem_mul_of_disjoint_leftCosets U₀ V g₀ gv
      (fun x hx ↦ hd0v x hx.1 hx.2))
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [mul_assoc] using congrArg (fun z ↦ g₀⁻¹ * z) hy
  · rcases hgv with ⟨y, ⟨u, hu, v, hv, rfl⟩, hy⟩
    apply (p43_inv_mul_notMem_mul_of_disjoint_leftCosets U₁ V g₁ gv
      (fun x hx ↦ hd1v x hx.1 hx.2))
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [mul_assoc] using congrArg (fun z ↦ g₁⁻¹ * z) hy
  · rcases hgv with ⟨y, ⟨u, hu, v, hv, rfl⟩, hy⟩
    apply (p43_inv_mul_notMem_mul_of_disjoint_leftCosets U₂ V g₂ gv
      (fun x hx ↦ hd2v x hx.1 hx.2))
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [mul_assoc] using congrArg (fun z ↦ g₂⁻¹ * z) hy

/-- Source Corollary 3.6, in the precise three-subgroup form used below. -/
private theorem p43_corollary36
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x))
    (hcard : Nat.card G ≤
      Nat.card ((V : Set G) * (U : Set G)) +
        Nat.card ((W : Set G) * (U : Set G)))
    (hsubset : (U : Set G) * (V : Set G) ⊆
      (W : Set G) * (V : Set G)) : False := by
  classical
  let A : Set G := b • ((V : Set G) * (U : Set G))
  let B : Set G := c • ((W : Set G) * (U : Set G))
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rcases hxA with ⟨yA, ⟨v, hv, u, hu, rfl⟩, hA⟩
    rcases hxB with ⟨yB, ⟨w, hw, u', hu', rfl⟩, hB⟩
    have hub : u' * u⁻¹ ∈ U := U.mul_mem hu' (U.inv_mem hu)
    have hvb : v⁻¹ ∈ V := V.inv_mem hv
    have hsmall : (u' * u⁻¹) * v⁻¹ ∈ (U : Set G) * (V : Set G) :=
      ⟨u' * u⁻¹, hub, v⁻¹, hvb, rfl⟩
    rcases hsubset hsmall with ⟨w', hw', v', hv', hwv'⟩
    have hnot := p43_inv_mul_notMem_mul_of_disjoint_leftCosets W V c b
      (by
        intro z hz
        exact hVW z ⟨hz.2, hz.1⟩)
    apply hnot
    refine ⟨w * w', W.mul_mem hw hw', v', hv', ?_⟩
    have heq : b * (v * u) = c * (w * u') := hA.trans hB.symm
    have hcb : c⁻¹ * b = w * ((u' * u⁻¹) * v⁻¹) := by
      have heq' := congrArg (fun z ↦ c⁻¹ * z * u⁻¹ * v⁻¹) heq
      simpa [mul_assoc] using heq'
    calc
      (w * w') * v' = w * (w' * v') := by simp [mul_assoc]
      _ = w * ((u' * u⁻¹) * v⁻¹) := by
        exact congrArg (fun z ↦ w * z) hwv'
      _ = c⁻¹ * b := hcb.symm
  have hcardUnion : (A ∪ B).ncard =
      Nat.card ((V : Set G) * (U : Set G)) +
        Nat.card ((W : Set G) * (U : Set G)) := by
    rw [Set.ncard_union_eq hAB]
    simp [A, B, Set.ncard_smul_set]
  have hunion : A ∪ B = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (s := A ∪ B) (t := Set.univ)
      (by intro x hx; trivial)
    rw [Set.ncard_univ, hcardUnion]
    exact hcard
  have ha : a ∈ A ∪ B := by rw [hunion]; trivial
  rcases ha with ha | ha
  · rcases ha with ⟨y, ⟨v, hv, u, hu, rfl⟩, hy⟩
    have hmem : b⁻¹ * a ∈ (V : Set G) * (U : Set G) := by
      refine ⟨v, hv, u, hu, ?_⟩
      simpa [mul_assoc] using congrArg (fun z ↦ b⁻¹ * z) hy
    exact (p43_inv_mul_notMem_mul_of_disjoint_leftCosets V U b a
      (by
        intro z hz
        exact hUV z ⟨hz.2, hz.1⟩)) hmem
  · rcases ha with ⟨y, ⟨w, hw, u, hu, rfl⟩, hy⟩
    have hmem : c⁻¹ * a ∈ (W : Set G) * (U : Set G) := by
      refine ⟨w, hw, u, hu, ?_⟩
      simpa [mul_assoc] using congrArg (fun z ↦ c⁻¹ * z) hy
    exact (p43_inv_mul_notMem_mul_of_disjoint_leftCosets W U c a
      (by
        intro z hz
        exact hUW z ⟨hz.2, hz.1⟩)) hmem

/-- For two disjoint cells with indices `3*r` and `3*s` and coprime
residuals, the source multiplier is either one or two. -/
theorem relIndex_eq_residual_or_twice_of_thrice_coprime
    {G : Type u} [Group G] (U V : Subgroup G) (a b : G)
    {r s : ℕ} (hU : U.index = 3 * r) (hV : V.index = 3 * s)
    (hcop : Nat.Coprime r s)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUfinite : U.index ≠ 0) :
    U.relIndex V = r ∨ U.relIndex V = 2 * r := by
  have hlt : U.relIndex V < 3 * r := by
    simpa [hU] using p43_relIndex_lt_index_of_disjoint_leftCosets
      U V a b hUfinite hdisjoint
  have hrelne : U.relIndex V ≠ 0 := by
    intro hzero
    exact hUfinite (U.index_eq_zero_of_relIndex_eq_zero hzero)
  have hdvdInter : U.index ∣ (U ⊓ V).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hdvdRaw : 3 * r ∣ U.relIndex V * (3 * s) := by
    rw [← hinter, hU, hV] at hdvdInter
    exact hdvdInter
  have hdvdThree : 3 * r ∣ 3 * (U.relIndex V * s) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvdRaw
  have hdr : r ∣ U.relIndex V * s :=
    Nat.dvd_of_mul_dvd_mul_left (by omega) hdvdThree
  have hdvd : r ∣ U.relIndex V :=
    hcop.dvd_of_dvd_mul_right hdr
  rcases hdvd with ⟨k, hk⟩
  have hrpos : 0 < r := by
    by_contra hr
    have : r = 0 := Nat.eq_zero_of_not_pos hr
    exact hUfinite (by simp [hU, this])
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    exact hrelne (by simpa [this] using hk)
  have hklt : k < 3 := by
    rw [hk] at hlt
    nlinarith
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (by simpa [mul_comm] using hk)

/-- The same multiplier occurs in both orientations of a pair. -/
theorem reverse_relIndex_eq_of_thrice_indices
    {G : Type u} [Group G] (U V : Subgroup G)
    {r s c : ℕ} (hU : U.index = 3 * r) (hV : V.index = 3 * s)
    (hrpos : 0 < r) (hforward : U.relIndex V = c * r) :
    V.relIndex U = c * s := by
  have hinterU : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hinterV : V.relIndex U * U.index = (U ⊓ V).index := by
    rw [inf_comm]
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := V ⊓ U) (K := U) inf_le_right)
  have hmul : (3 * r) * (c * s) = (3 * r) * V.relIndex U := by
    calc
      (3 * r) * (c * s) = (c * r) * (3 * s) := by ring
      _ = (U ⊓ V).index := by rw [← hinterU, hforward, hV]
      _ = V.relIndex U * (3 * r) := by rw [← hinterV, hU]
      _ = (3 * r) * V.relIndex U := by ring
  exact (Nat.mul_left_cancel (by omega) hmul).symm

/-! ## The two mixed-triangle calculations

The published proof packages these calculations through Lemma 3.10 and
Corollary 3.11.  We keep the exact special case needed by Proposition 4.3
explicit.  This has two advantages: every cancellation is visible in Lean,
and the proof does not rely on the overly compressed last inference in the
printed proof of Corollary 3.11.
-/

/-- Arithmetic data behind Lemma 3.10(a), specialized to common factor three.

If the `U-V` multiplier is one and the `U-W` multiplier is two, write the
relative index of the triple intersection inside `W` as `rw * k`.  Then `k`
is positive, is at most the `V-W` multiplier `c`, and `2 ∣ k * rv`.
-/
private theorem p43_triple_multiplier_data
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
    by_contra h
    have : ru = 0 := Nat.eq_zero_of_not_pos h
    exact hUfinite (by simp [hU, this])
  have hrvpos : 0 < rv := by
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hrwpos : 0 < rw := by
    by_contra h
    have : rw = 0 := Nat.eq_zero_of_not_pos h
    exact hWfinite (by simp [hW, this])
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
  have hrwDivProduct : rw ∣ W.relIndex (U ⊓ V) * rv := by
    exact (show rw ∣ 2 * rw by exact ⟨2, by omega⟩).trans hcancel
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
    exact p43_reverse_relIndex_eq_of_thrice_indices V W hV hW hrvpos
      (by simpa [mul_comm] using hrelVW)
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

/-- A triangle with multipliers `1,2,1` forces the residual at the vertex
between the two multiplier-one edges to be even. -/
private theorem p43_even_middle_of_one_two_one
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hrvrw : Nat.Coprime rv rw)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = rv) : Even rv := by
  rcases p43_triple_multiplier_data (c := 1) U V W hU hV hW hrvrw
      hrelUV hrelUW (by simpa using hrelVW) with
    ⟨k, -, hkpos, hkle, htwo⟩
  have hk : k = 1 := by omega
  rw [hk, one_mul] at htwo
  exact even_iff_two_dvd.mpr htwo

/-- If the mixed triangle has multipliers `1,2,2` and the middle residual is
odd, the triple-intersection relative index attains its upper bound. -/
private theorem p43_triple_relIndex_eq_twice_of_odd_middle
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
  rcases p43_triple_multiplier_data U V W hU hV hW hrvrw
      hrelUV hrelUW hrelVW with
    ⟨k, hk, hkpos, hkle, htwo⟩
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl
  · exact False.elim (hrvOdd (even_iff_two_dvd.mpr (by simpa using htwo)))
  · simpa [mul_comm] using hk

/-- The equality case behind Lemma 3.10(b), in the sole form needed here. -/
private theorem p43_inf_mul_eq_of_one_two_two_odd_middle
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
  have htriple := p43_triple_relIndex_eq_twice_of_odd_middle
    U V W hU hV hW hrvrw hrelUV hrelUW hrelVW hrvOdd
  have hrvpos : 0 < rv := by
    have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hrevVW : W.relIndex V = 2 * rw := by
    exact p43_reverse_relIndex_eq_of_thrice_indices V W hV hW hrvpos
      (by simpa using hrelVW)
  have hsubset : ((U ⊓ V : Subgroup G) : Set G) * (W : Set G) ⊆
      (V : Set G) * (W : Set G) := by
    rintro x ⟨z, hz, w, hw, rfl⟩
    exact ⟨z, hz.2, w, hw, rfl⟩
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    p43_natCard_subgroup_mul, p43_natCard_subgroup_mul,
    htriple, hrevVW]

/-- Claim 1 of Proposition 4.3, with the harmless missing parity split made
explicit, first when the middle residual is odd. -/
private theorem p43_no_one_two_two_of_odd_middle
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
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hruPos : 0 < ru := by
    have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have : ru = 0 := Nat.eq_zero_of_not_pos h
    exact hUfinite (by simp [hU, this])
  have heq := p43_inf_mul_eq_of_one_two_two_odd_middle
    U V W hU hV hW hrvrw hrelUV hrelUW hrelVW hrvOdd
  have hsubset : (V : Set G) * (W : Set G) ⊆
      (U : Set G) * (W : Set G) := by
    rw [← heq]
    rintro x ⟨z, hz, w, hw, rfl⟩
    exact ⟨z, hz.1, w, hw, rfl⟩
  have hrevUV : V.relIndex U = rv := by
    simpa using (p43_reverse_relIndex_eq_of_thrice_indices U V (c := 1)
      hU hV hruPos (by simpa using hrelUV))
  have hcardWV := p43_three_mul_natCard_mul_eq W V hV hrelVW
  have hcardUV := p43_three_mul_natCard_mul_eq U V (c := 1) hV
    (by simpa using hrevUV)
  have hcard : Nat.card G ≤
      Nat.card ((W : Set G) * (V : Set G)) +
        Nat.card ((U : Set G) * (V : Set G)) := by omega
  exact p43_corollary36 V W U b c a hVW
    (fun x hx ↦ hUV x ⟨hx.2, hx.1⟩)
    (fun x hx ↦ hUW x ⟨hx.2, hx.1⟩) hcard hsubset

/-- Claim 1 of Proposition 4.3: a harmonic triangle cannot have multipliers
`1,2,2`.  Pairwise coprimality guarantees that one endpoint of the
multiplier-one edge has odd residual, so the preceding lemma applies after at
most swapping the endpoints. -/
private theorem p43_no_one_two_two
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
      by_contra h
      have : ru = 0 := Nat.eq_zero_of_not_pos h
      exact hUfinite (by simp [hU, this])
    have hrevUV : V.relIndex U = rv := by
      simpa using (p43_reverse_relIndex_eq_of_thrice_indices U V (c := 1)
        hU hV hruPos (by simpa using hrelUV))
    exact p43_no_one_two_two_of_odd_middle V U W b a c hV hU hW
      hruw hrevUV hrelVW hrelUW
      (fun x hx ↦ hUV x ⟨hx.2, hx.1⟩) hVW hUW hruOdd
  · exact p43_no_one_two_two_of_odd_middle U V W a b c hU hV hW
      hrvrw hrelUV hrelUW hrelVW hUV hUW hVW hrvEven

/-- Package six explicitly oriented disjointness statements as a harmonic
`Fin 4` family.  Keeping this constructor local makes later permutations of
the four vertices transparent. -/
private theorem p43_harmonic_fin4_of_six
    {G : Type u} [Group G]
    (g₀ g₁ g₂ g₃ : G) (U₀ U₁ U₂ U₃ : Subgroup G)
    (h01 : ∀ x, ¬(InLeftCoset g₀ U₀ x ∧ InLeftCoset g₁ U₁ x))
    (h02 : ∀ x, ¬(InLeftCoset g₀ U₀ x ∧ InLeftCoset g₂ U₂ x))
    (h03 : ∀ x, ¬(InLeftCoset g₀ U₀ x ∧ InLeftCoset g₃ U₃ x))
    (h12 : ∀ x, ¬(InLeftCoset g₁ U₁ x ∧ InLeftCoset g₂ U₂ x))
    (h13 : ∀ x, ¬(InLeftCoset g₁ U₁ x ∧ InLeftCoset g₃ U₃ x))
    (h23 : ∀ x, ¬(InLeftCoset g₂ U₂ x ∧ InLeftCoset g₃ U₃ x)) :
    IsHarmonicCosetFamily ![g₀, g₁, g₂, g₃] ![U₀, U₁, U₂, U₃] := by
  intro i j hij x hx
  fin_cases i <;> fin_cases j <;> simp at hij hx ⊢
  all_goals first
    | exact h01 x hx
    | exact h01 x ⟨hx.2, hx.1⟩
    | exact h02 x hx
    | exact h02 x ⟨hx.2, hx.1⟩
    | exact h03 x hx
    | exact h03 x ⟨hx.2, hx.1⟩
    | exact h12 x hx
    | exact h12 x ⟨hx.2, hx.1⟩
    | exact h13 x hx
    | exact h13 x ⟨hx.2, hx.1⟩
    | exact h23 x hx
    | exact h23 x ⟨hx.2, hx.1⟩

/-- Claim 2 of Proposition 4.3: inside a harmonic four-family, a triangle
cannot have multipliers `2,1,1`.  The opposite residual is forced even; the
fourth vertex then either forces a second even residual or supplies the
three multiplier-one spokes excluded by Proposition 3.8. -/
private theorem p43_no_two_one_one_four
    {G : Type u} [Group G] [Finite G]
    (U V W X : Subgroup G) (a b c d : G) {ru rv rw rx : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw) (hX : X.index = 3 * rx)
    (hruv : Nat.Coprime ru rv) (hruw : Nat.Coprime ru rw)
    (hrux : Nat.Coprime ru rx) (hrvw : Nat.Coprime rv rw)
    (hrvx : Nat.Coprime rv rx) (hrwx : Nat.Coprime rw rx)
    (hrelUV : U.relIndex V = 2 * ru)
    (hrelUW : U.relIndex W = ru)
    (hrelVW : V.relIndex W = rv)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hUX : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset d X x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x))
    (hVX : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset d X x))
    (hWX : ∀ x, ¬(InLeftCoset c W x ∧ InLeftCoset d X x)) : False := by
  have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hWfinite : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hXfinite : X.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrupos : 0 < ru := by
    by_contra h
    have : ru = 0 := Nat.eq_zero_of_not_pos h
    exact hUfinite (by simp [hU, this])
  have hrvpos : 0 < rv := by
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hrwpos : 0 < rw := by
    by_contra h
    have : rw = 0 := Nat.eq_zero_of_not_pos h
    exact hWfinite (by simp [hW, this])
  have hrxpos : 0 < rx := by
    by_contra h
    have : rx = 0 := Nat.eq_zero_of_not_pos h
    exact hXfinite (by simp [hX, this])
  have hrevUV : V.relIndex U = 2 * rv :=
    p43_reverse_relIndex_eq_of_thrice_indices U V (c := 2)
      hU hV hrupos hrelUV
  have hrevUW : W.relIndex U = rw := by
    simpa using (p43_reverse_relIndex_eq_of_thrice_indices U W (c := 1)
      hU hW hrupos (by simpa using hrelUW))
  have hrevVW : W.relIndex V = rw := by
    simpa using (p43_reverse_relIndex_eq_of_thrice_indices V W (c := 1)
      hV hW hrvpos (by simpa using hrelVW))
  have hWEven : Even rw :=
    p43_even_middle_of_one_two_one U W V hU hW hV hrvw.symm
      hrelUW hrelUV hrevVW
  have hUXcases := relIndex_eq_residual_or_twice_of_thrice_coprime
    U X a d hU hX hrux hUX hUfinite
  have hVXcases := relIndex_eq_residual_or_twice_of_thrice_coprime
    V X b d hV hX hrvx hVX hVfinite
  rcases hUXcases with hrelUX | hrelUX <;>
    rcases hVXcases with hrelVX | hrelVX
  · -- Both fourth-vertex edges have multiplier one, forcing `rx` even.
    have hrevXV : X.relIndex V = rx := by
      simpa using (p43_reverse_relIndex_eq_of_thrice_indices V X (c := 1)
        hV hX hrvpos (by simpa using hrelVX))
    have hXEven : Even rx :=
      p43_even_middle_of_one_two_one U X V hU hX hV hrvx.symm
        hrelUX hrelUV hrevXV
    have htwoGcd : 2 ∣ Nat.gcd rw rx :=
      Nat.dvd_gcd hWEven.two_dvd hXEven.two_dvd
    rw [hrwx.gcd_eq_one] at htwoGcd
    norm_num at htwoGcd
  · -- Multipliers `1,2` to `X` make a forbidden `1,2,2` triangle.
    have hrevXV : X.relIndex V = 2 * rx :=
      p43_reverse_relIndex_eq_of_thrice_indices V X (c := 2)
        hV hX hrvpos hrelVX
    exact p43_no_one_two_two U X V a d b hU hX hV hrux hruv
      hrvx.symm hrelUX hrelUV hrevXV hUX hUV
      (fun x hx ↦ hVX x ⟨hx.2, hx.1⟩)
  · -- The symmetric `2,1` assignment is forbidden for the same reason.
    have hrevXU : X.relIndex U = 2 * rx :=
      p43_reverse_relIndex_eq_of_thrice_indices U X (c := 2)
        hU hX hrupos hrelUX
    exact p43_no_one_two_two V X U b d a hV hX hU hrvx hruv.symm
      hrux.symm hrelVX hrevUV hrevXU hVX
      (fun x hx ↦ hUV x ⟨hx.2, hx.1⟩)
      (fun x hx ↦ hUX x ⟨hx.2, hx.1⟩)
  · -- Both edges to `X` have multiplier two.  Claim 1 forces `W-X` to
    -- have multiplier one, giving three multiplier-one spokes at `W`.
    have hWXcases := relIndex_eq_residual_or_twice_of_thrice_coprime
      W X c d hW hX hrwx hWX hWfinite
    rcases hWXcases with hrelWX | hrelWX
    · have hrevXW : X.relIndex W = rx := by
        simpa using (p43_reverse_relIndex_eq_of_thrice_indices W X (c := 1)
          hW hX hrwpos (by simpa using hrelWX))
      have hharmonic := p43_harmonic_fin4_of_six a b d c U V X W
        hUV hUX hUW hVX hVW (fun x hx ↦ hWX x ⟨hx.2, hx.1⟩)
      exact p43_proposition38_three U V X W a b d c hU hV hX hW
        hruv hrux hruw hrvx hrvw hrwx.symm
        hrelUW hrelVW hrevXW hharmonic
    · exact p43_no_one_two_two V W X b c d hV hW hX hrvw hrvx
        hrwx hrelVW hrelVX hrelWX hVW hVX hWX

/-! ## The all-two case -/

/-- Right translation by `x⁻¹` identifies a double coset `U x A` with the
product of `U` and the conjugate `x A x⁻¹`. -/
private theorem p43_natCard_doubleCoset_eq_conjugate_product
    {G : Type u} [Group G] (U A : Subgroup G) (x : G) :
    Nat.card (DoubleCoset.doubleCoset x U A) =
      Nat.card ((U : Set G) *
        ((A.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) := by
  let P : Subgroup G := A.map (MulAut.conj x).toMonoidHom
  let e : (DoubleCoset.doubleCoset x U A) ≃
      ((U : Set G) * (P : Set G)) :=
    { toFun := fun y ↦ ⟨(y : G) * x⁻¹, by
        rcases DoubleCoset.mem_doubleCoset.mp y.property with
          ⟨u, hu, a, ha, hy⟩
        rw [hy]
        refine ⟨u, hu, x * a * x⁻¹, ?_, ?_⟩
        · change x * a * x⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom
          refine ⟨a, ha, ?_⟩
          simp [MulAut.conj_apply]
        · simp [mul_assoc]⟩
      invFun := fun y ↦ ⟨(y : G) * x, by
        rcases y.property with ⟨u, hu, p, hp, hy⟩
        rw [← hy]
        change p ∈ A.map (MulAut.conj x).toMonoidHom at hp
        rcases hp with ⟨a, ha, rfl⟩
        apply DoubleCoset.mem_doubleCoset.mpr
        refine ⟨u, hu, a, ha, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]⟩
      left_inv := by
        intro y
        apply Subtype.ext
        simp
      right_inv := by
        intro y
        apply Subtype.ext
        simp }
  change Nat.card (DoubleCoset.doubleCoset x U A) =
    Nat.card ((U : Set G) * (P : Set G))
  exact Nat.card_congr e

/-- If `[G:U]=3*ru`, `[G:A]=6*s`, and `ru` is coprime to `2*s`, every
`U-A` double coset occupies at least one third of the finite group. -/
private theorem p43_natCard_le_three_mul_doubleCoset
    {G : Type u} [Group G] [Finite G]
    (U A : Subgroup G) (x : G) {ru s : ℕ}
    (hU : U.index = 3 * ru) (hA : A.index = 6 * s)
    (hcop : Nat.Coprime ru (2 * s)) :
    Nat.card G ≤ 3 * Nat.card (DoubleCoset.doubleCoset x U A) := by
  let P : Subgroup G := A.map (MulAut.conj x).toMonoidHom
  have hPindex : P.index = 6 * s := by
    calc
      P.index = A.index := by
        simpa [P] using (Subgroup.index_map_equiv (MulAut.conj x) A)
      _ = 6 * s := hA
  have hinter : P.relIndex U * U.index = (P ⊓ U).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := P ⊓ U) (K := U) inf_le_right)
  have hraw : P.index ∣ (P ⊓ U).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hfactor : 3 * (2 * s) ∣ 3 * (P.relIndex U * ru) := by
    rw [hPindex, ← hinter, hU] at hraw
    simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
  have hcancel : 2 * s ∣ P.relIndex U * ru :=
    Nat.dvd_of_mul_dvd_mul_left (by omega) hfactor
  have hdiv : 2 * s ∣ P.relIndex U :=
    hcop.symm.dvd_of_dvd_mul_right hcancel
  have hspos : 0 < s := by
    have hAfinite : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have : s = 0 := Nat.eq_zero_of_not_pos h
    exact hAfinite (by simp [hA, this])
  have hrelLower : 2 * s ≤ P.relIndex U :=
    Nat.le_of_dvd (by
      have hPne : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hrelNe : P.relIndex U ≠ 0 := by
        intro hz
        exact hPne (P.index_eq_zero_of_relIndex_eq_zero hz)
      omega) hdiv
  have hcardP := P.index_mul_card
  rw [hPindex] at hcardP
  rw [p43_natCard_doubleCoset_eq_conjugate_product,
    p43_natCard_subgroup_mul]
  nlinarith

/-- Strong form of the preceding bound: three times a double-coset size is a
positive integral multiple of the ambient group order. -/
private theorem p43_three_mul_natCard_doubleCoset_eq_multiple
    {G : Type u} [Group G] [Finite G]
    (U A : Subgroup G) (x : G) {ru s : ℕ}
    (hU : U.index = 3 * ru) (hA : A.index = 6 * s)
    (hcop : Nat.Coprime ru (2 * s)) :
    ∃ k : ℕ, 0 < k ∧
      3 * Nat.card (DoubleCoset.doubleCoset x U A) = k * Nat.card G := by
  let P : Subgroup G := A.map (MulAut.conj x).toMonoidHom
  have hPindex : P.index = 6 * s := by
    calc
      P.index = A.index := by
        simpa [P] using (Subgroup.index_map_equiv (MulAut.conj x) A)
      _ = 6 * s := hA
  have hinter : P.relIndex U * U.index = (P ⊓ U).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := P ⊓ U) (K := U) inf_le_right)
  have hraw : P.index ∣ (P ⊓ U).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hfactor : 3 * (2 * s) ∣ 3 * (P.relIndex U * ru) := by
    rw [hPindex, ← hinter, hU] at hraw
    simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
  have hcancel : 2 * s ∣ P.relIndex U * ru :=
    Nat.dvd_of_mul_dvd_mul_left (by omega) hfactor
  have hdiv : 2 * s ∣ P.relIndex U :=
    hcop.symm.dvd_of_dvd_mul_right hcancel
  rcases hdiv with ⟨k, hk⟩
  have hPne : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrelNe : P.relIndex U ≠ 0 := by
    intro hz
    exact hPne (P.index_eq_zero_of_relIndex_eq_zero hz)
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := Nat.eq_zero_of_not_pos h
    exact hrelNe (by simpa [this] using hk)
  have hcardP := P.index_mul_card
  rw [hPindex] at hcardP
  refine ⟨k, hkpos, ?_⟩
  rw [p43_natCard_doubleCoset_eq_conjugate_product,
    p43_natCard_subgroup_mul, hk]
  nlinarith

/-- Inversion reverses both subgroup factors of a product-set equality. -/
private theorem p43_reverse_subgroup_product_eq
    {G : Type u} [Group G] (U V W : Subgroup G)
    (h : (U : Set G) * (V : Set G) =
      (U : Set G) * (W : Set G)) :
    (V : Set G) * (U : Set G) = (W : Set G) * (U : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, u, hu, rfl⟩
    have hinv : (u⁻¹ * v⁻¹ : G) ∈ (U : Set G) * (V : Set G) :=
      ⟨u⁻¹, U.inv_mem hu, v⁻¹, V.inv_mem hv, rfl⟩
    rw [h] at hinv
    rcases hinv with ⟨u', hu', w, hw, huw⟩
    refine ⟨w⁻¹, W.inv_mem hw, u'⁻¹, U.inv_mem hu', ?_⟩
    change u' * w = u⁻¹ * v⁻¹ at huw
    have := congrArg Inv.inv huw
    simpa [mul_inv_rev] using this
  · rintro ⟨w, hw, u, hu, rfl⟩
    have hinv : (u⁻¹ * w⁻¹ : G) ∈ (U : Set G) * (W : Set G) :=
      ⟨u⁻¹, U.inv_mem hu, w⁻¹, W.inv_mem hw, rfl⟩
    rw [← h] at hinv
    rcases hinv with ⟨u', hu', v, hv, huv⟩
    refine ⟨v⁻¹, V.inv_mem hv, u'⁻¹, U.inv_mem hu', ?_⟩
    change u' * v = u⁻¹ * w⁻¹ at huv
    have := congrArg Inv.inv huv
    simpa [mul_inv_rev] using this

/-- With all three pair multipliers equal to two, the two products sharing a
left factor cannot coincide; otherwise Corollary 3.6 gives a packing
contradiction. -/
private theorem p43_all_two_products_ne
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hrelUV : U.relIndex V = 2 * ru)
    (hrelVW : V.relIndex W = 2 * rv)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x)) :
    (U : Set G) * (V : Set G) ≠ (U : Set G) * (W : Set G) := by
  intro heq
  have hrupos : 0 < ru := by
    have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have : ru = 0 := Nat.eq_zero_of_not_pos h
    exact hUfinite (by simp [hU, this])
  have hrevUV : V.relIndex U = 2 * rv :=
    p43_reverse_relIndex_eq_of_thrice_indices U V (c := 2)
      hU hV hrupos hrelUV
  have hcardUV := p43_three_mul_natCard_mul_eq U V hV hrevUV
  have hcardWV := p43_three_mul_natCard_mul_eq W V hV hrelVW
  have hcard : Nat.card G ≤
      Nat.card ((U : Set G) * (V : Set G)) +
        Nat.card ((W : Set G) * (V : Set G)) := by omega
  have hreverse := p43_reverse_subgroup_product_eq U V W heq
  exact p43_corollary36 V U W b a c
    (fun x hx ↦ hUV x ⟨hx.2, hx.1⟩) hVW hUW hcard
    (by rw [hreverse])

/-- The intersection `UV ∩ UW` is stable under left multiplication by `U`
and right multiplication by `V ∩ W`; hence it contains the full corresponding
double coset through each of its points. -/
private theorem p43_doubleCoset_subset_inter_products
    {G : Type u} [Group G] (U V W : Subgroup G) (x : G)
    (hx : x ∈ ((U : Set G) * (V : Set G)) ∩
      ((U : Set G) * (W : Set G))) :
    DoubleCoset.doubleCoset x U (V ⊓ W) ⊆
      ((U : Set G) * (V : Set G)) ∩
        ((U : Set G) * (W : Set G)) := by
  intro y hy
  rcases DoubleCoset.mem_doubleCoset.mp hy with ⟨u, hu, z, hz, hy⟩
  rcases hx.1 with ⟨uV, huV, v, hv, hxV⟩
  rcases hx.2 with ⟨uW, huW, w, hw, hxW⟩
  rw [hy]
  constructor
  · refine ⟨u * uV, U.mul_mem hu huV, v * z, V.mul_mem hv hz.1, ?_⟩
    rw [← hxV]
    simp [mul_assoc]
  · refine ⟨u * uW, U.mul_mem hu huW, w * z, W.mul_mem hw hz.2, ?_⟩
    rw [← hxW]
    simp [mul_assoc]

/-- For an odd anchor residual, two all-multiplier-two products sharing the
anchor cover the finite group.  This is the repaired double-coset step in the
last paragraph of Proposition 4.3: oddness makes every relevant double-coset
block a positive multiple of one third of the group. -/
private theorem p43_all_two_product_union_eq_univ
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G) {ru rv rw : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw)
    (hruv : Nat.Coprime ru rv) (hruw : Nat.Coprime ru rw)
    (hrvrw : Nat.Coprime rv rw)
    (hruOdd : ¬ Even ru)
    (hrelUV : U.relIndex V = 2 * ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelVW : V.relIndex W = 2 * rv)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x)) :
    ((U : Set G) * (V : Set G)) ∪
      ((U : Set G) * (W : Set G)) = Set.univ := by
  let A : Subgroup G := V ⊓ W
  let R : Set G := (U : Set G) * (V : Set G)
  let S : Set G := (U : Set G) * (W : Set G)
  let D : Set G := DoubleCoset.doubleCoset 1 U A
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hrupos : 0 < ru := by
    have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have : ru = 0 := Nat.eq_zero_of_not_pos h
    exact hUfinite (by simp [hU, this])
  have hrvpos : 0 < rv := by
    have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hAindex : A.index = 6 * (rv * rw) := by
    have h := Subgroup.relIndex_mul_index
      (H := V ⊓ W) (K := W) inf_le_right
    simp only [Subgroup.inf_relIndex_right] at h
    rw [hrelVW, hW] at h
    change (V ⊓ W).index = 6 * (rv * rw)
    nlinarith
  have hruOdd' : Odd ru := Nat.not_even_iff_odd.mp hruOdd
  have hcopBlock : Nat.Coprime ru (2 * (rv * rw)) :=
    hruOdd'.coprime_two_right.mul_right (hruv.mul_right hruw)
  have hrevUV : V.relIndex U = 2 * rv :=
    p43_reverse_relIndex_eq_of_thrice_indices U V (c := 2)
      hU hV hrupos hrelUV
  have hrevUW : W.relIndex U = 2 * rw :=
    p43_reverse_relIndex_eq_of_thrice_indices U W (c := 2)
      hU hW hrupos hrelUW
  have hRcard0 := p43_three_mul_natCard_mul_eq U V hV hrevUV
  have hScard0 := p43_three_mul_natCard_mul_eq U W hW hrevUW
  have hRcard : 3 * R.ncard = 2 * Nat.card G := by
    simpa [R, Nat.card_coe_set_eq] using hRcard0
  have hScard : 3 * S.ncard = 2 * Nat.card G := by
    simpa [S, Nat.card_coe_set_eq] using hScard0
  have hRneS : R ≠ S := by
    simpa [R, S] using p43_all_two_products_ne U V W a b c
      hU hV hW hrelUV hrelVW hUV hUW hVW
  have honeInter : (1 : G) ∈ R ∩ S := by
    constructor
    · exact ⟨1, U.one_mem, 1, V.one_mem, by simp [R]⟩
    · exact ⟨1, U.one_mem, 1, W.one_mem, by simp [S]⟩
  have hDsubInter : D ⊆ R ∩ S := by
    simpa [D, A, R, S] using
      p43_doubleCoset_subset_inter_products U V W 1 honeInter
  have hDsubR : D ⊆ R := hDsubInter.trans Set.inter_subset_left
  have hDsubS : D ⊆ S := hDsubInter.trans Set.inter_subset_right
  rcases p43_three_mul_natCard_doubleCoset_eq_multiple U A 1 hU hAindex
      hcopBlock with ⟨k, hkpos, hDcard0⟩
  have hDcard : 3 * D.ncard = k * Nat.card G := by
    simpa [D, Nat.card_coe_set_eq] using hDcard0
  have hDleR : D.ncard ≤ R.ncard := Set.ncard_le_ncard hDsubR
  have hkle : k ≤ 2 := by nlinarith
  have hk : k = 1 := by
    have hkCases : k = 1 ∨ k = 2 := by omega
    rcases hkCases with hk | hk
    · exact hk
    · exfalso
      rw [hk] at hDcard
      have hDRcard : D.ncard = R.ncard := by omega
      have hDeqR : D = R :=
        Set.eq_of_subset_of_ncard_le hDsubR hDRcard.ge
      have hRsubS : R ⊆ S := by rw [← hDeqR]; exact hDsubS
      have hRScard : R.ncard = S.ncard := by omega
      have hReqS : R = S :=
        Set.eq_of_subset_of_ncard_le hRsubS hRScard.ge
      exact hRneS hReqS
  have hDthird : 3 * D.ncard = Nat.card G := by simpa [hk] using hDcard
  have hInterSubD : R ∩ S ⊆ D := by
    intro x hx
    by_contra hxD
    let E : Set G := DoubleCoset.doubleCoset x U A
    have hEsubInter : E ⊆ R ∩ S := by
      simpa [E, A, R, S] using
        p43_doubleCoset_subset_inter_products U V W x hx
    have hEsubR : E ⊆ R := hEsubInter.trans Set.inter_subset_left
    have hEsubS : E ⊆ S := hEsubInter.trans Set.inter_subset_right
    have hDE : Disjoint D E := by
      by_contra hnot
      apply hxD
      exact DoubleCoset.mem_doubleCoset_of_not_disjoint
        (by simpa [D, E, A] using hnot)
    rcases p43_three_mul_natCard_doubleCoset_eq_multiple U A x hU hAindex
        hcopBlock with ⟨m, hmpos, hEcard0⟩
    have hEcard : 3 * E.ncard = m * Nat.card G := by
      simpa [E, Nat.card_coe_set_eq] using hEcard0
    have hElower : Nat.card G ≤ 3 * E.ncard := by
      calc
        Nat.card G = 1 * Nat.card G := by simp
        _ ≤ m * Nat.card G := Nat.mul_le_mul_right (Nat.card G) hmpos
        _ = 3 * E.ncard := hEcard.symm
    have hUnionSubR : D ∪ E ⊆ R := Set.union_subset hDsubR hEsubR
    have hUnionSubS : D ∪ E ⊆ S := Set.union_subset hDsubS hEsubS
    have hUnionCard : (D ∪ E).ncard = D.ncard + E.ncard :=
      Set.ncard_union_eq hDE
    have hUnionLeR : (D ∪ E).ncard ≤ R.ncard :=
      Set.ncard_le_ncard hUnionSubR
    have hUnionEqRcard : (D ∪ E).ncard = R.ncard := by omega
    have hUnionEqR : D ∪ E = R :=
      Set.eq_of_subset_of_ncard_le hUnionSubR hUnionEqRcard.ge
    have hRsubS : R ⊆ S := by rw [← hUnionEqR]; exact hUnionSubS
    have hRScard : R.ncard = S.ncard := by omega
    have hReqS : R = S :=
      Set.eq_of_subset_of_ncard_le hRsubS hRScard.ge
    exact hRneS hReqS
  have hInterEqD : R ∩ S = D :=
    Set.Subset.antisymm hInterSubD hDsubInter
  have hInterCard : 3 * (R ∩ S).ncard = Nat.card G := by
    rw [hInterEqD]
    exact hDthird
  have hUnionInter := Set.ncard_union_add_ncard_inter R S
  have hUnionCard : (R ∪ S).ncard = Nat.card G := by omega
  have hUnionEq : R ∪ S = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ (R ∪ S))
    rw [Set.ncard_univ, hUnionCard]
  simpa [R, S] using hUnionEq

/-- Three two-thirds subsets of a finite set whose pairwise unions are the
whole set have empty triple intersection. -/
private theorem p43_triple_inter_eq_empty_of_pair_unions
    {α : Type u} [Finite α] (R S T : Set α)
    (hRcard : 3 * R.ncard = 2 * Nat.card α)
    (hScard : 3 * S.ncard = 2 * Nat.card α)
    (hTcard : 3 * T.ncard = 2 * Nat.card α)
    (hRS : R ∪ S = Set.univ) (hRT : R ∪ T = Set.univ)
    (hST : S ∪ T = Set.univ) : R ∩ S ∩ T = ∅ := by
  have hRc := Set.ncard_add_ncard_compl R
  have hSc := Set.ncard_add_ncard_compl S
  have hTc := Set.ncard_add_ncard_compl T
  have hRcomp : 3 * Rᶜ.ncard = Nat.card α := by omega
  have hScomp : 3 * Sᶜ.ncard = Nat.card α := by omega
  have hTcomp : 3 * Tᶜ.ncard = Nat.card α := by omega
  have hdRS : Disjoint Rᶜ Sᶜ := by
    rw [Set.disjoint_left]
    intro x hxR hxS
    have hx : x ∈ R ∪ S := by rw [hRS]; trivial
    rcases hx with hx | hx
    · exact hxR hx
    · exact hxS hx
  have hdRT : Disjoint Rᶜ Tᶜ := by
    rw [Set.disjoint_left]
    intro x hxR hxT
    have hx : x ∈ R ∪ T := by rw [hRT]; trivial
    rcases hx with hx | hx
    · exact hxR hx
    · exact hxT hx
  have hdST : Disjoint Sᶜ Tᶜ := by
    rw [Set.disjoint_left]
    intro x hxS hxT
    have hx : x ∈ S ∪ T := by rw [hST]; trivial
    rcases hx with hx | hx
    · exact hxS hx
    · exact hxT hx
  have hdUnion : Disjoint (Rᶜ ∪ Sᶜ) Tᶜ :=
    Set.disjoint_union_left.2 ⟨hdRT, hdST⟩
  have hCompUnionCard : ((Rᶜ ∪ Sᶜ) ∪ Tᶜ).ncard = Nat.card α := by
    rw [Set.ncard_union_eq hdUnion, Set.ncard_union_eq hdRS]
    omega
  have hCover : (Rᶜ ∪ Sᶜ) ∪ Tᶜ = Set.univ :=
    (Set.eq_univ_iff_ncard ((Rᶜ ∪ Sᶜ) ∪ Tᶜ)).mpr hCompUnionCard
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxComp : x ∈ (Rᶜ ∪ Sᶜ) ∪ Tᶜ := by rw [hCover]; trivial
  rcases hxComp with (hxR | hxS) | hxT
  · exact hxR hx.1.1
  · exact hxS hx.1.2
  · exact hxT hx.2

/-- The all-multiplier-two case is impossible once an odd residual is chosen
as anchor.  The three anchor products pairwise cover `G`, yet their common
intersection contains the anchor subgroup. -/
private theorem p43_no_all_two_of_odd_anchor
    {G : Type u} [Group G] [Finite G]
    (U V W X : Subgroup G) (a b c d : G) {ru rv rw rx : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw) (hX : X.index = 3 * rx)
    (hruv : Nat.Coprime ru rv) (hruw : Nat.Coprime ru rw)
    (hrux : Nat.Coprime ru rx) (hrvw : Nat.Coprime rv rw)
    (hrvx : Nat.Coprime rv rx) (hrwx : Nat.Coprime rw rx)
    (hruOdd : ¬ Even ru)
    (hrelUV : U.relIndex V = 2 * ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hrelUX : U.relIndex X = 2 * ru)
    (hrelVW : V.relIndex W = 2 * rv)
    (hrelVX : V.relIndex X = 2 * rv)
    (hrelWX : W.relIndex X = 2 * rw)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hUX : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset d X x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x))
    (hVX : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset d X x))
    (hWX : ∀ x, ¬(InLeftCoset c W x ∧ InLeftCoset d X x)) : False := by
  let R : Set G := (U : Set G) * (V : Set G)
  let S : Set G := (U : Set G) * (W : Set G)
  let T : Set G := (U : Set G) * (X : Set G)
  have hRS : R ∪ S = Set.univ := by
    simpa [R, S] using p43_all_two_product_union_eq_univ U V W a b c
      hU hV hW hruv hruw hrvw hruOdd hrelUV hrelUW hrelVW hUV hUW hVW
  have hRT : R ∪ T = Set.univ := by
    simpa [R, T] using p43_all_two_product_union_eq_univ U V X a b d
      hU hV hX hruv hrux hrvx hruOdd hrelUV hrelUX hrelVX hUV hUX hVX
  have hST : S ∪ T = Set.univ := by
    simpa [S, T] using p43_all_two_product_union_eq_univ U W X a c d
      hU hW hX hruw hrux hrwx hruOdd hrelUW hrelUX hrelWX hUW hUX hWX
  have hrupos : 0 < ru := by
    have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have : ru = 0 := Nat.eq_zero_of_not_pos h
    exact hUfinite (by simp [hU, this])
  have hrevUV : V.relIndex U = 2 * rv :=
    p43_reverse_relIndex_eq_of_thrice_indices U V (c := 2)
      hU hV hrupos hrelUV
  have hrevUW : W.relIndex U = 2 * rw :=
    p43_reverse_relIndex_eq_of_thrice_indices U W (c := 2)
      hU hW hrupos hrelUW
  have hrevUX : X.relIndex U = 2 * rx :=
    p43_reverse_relIndex_eq_of_thrice_indices U X (c := 2)
      hU hX hrupos hrelUX
  have hRcard0 := p43_three_mul_natCard_mul_eq U V hV hrevUV
  have hScard0 := p43_three_mul_natCard_mul_eq U W hW hrevUW
  have hTcard0 := p43_three_mul_natCard_mul_eq U X hX hrevUX
  have hRcard : 3 * R.ncard = 2 * Nat.card G := by
    simpa [R, Nat.card_coe_set_eq] using hRcard0
  have hScard : 3 * S.ncard = 2 * Nat.card G := by
    simpa [S, Nat.card_coe_set_eq] using hScard0
  have hTcard : 3 * T.ncard = 2 * Nat.card G := by
    simpa [T, Nat.card_coe_set_eq] using hTcard0
  have hEmpty := p43_triple_inter_eq_empty_of_pair_unions R S T
    hRcard hScard hTcard hRS hRT hST
  have hone : (1 : G) ∈ R ∩ S ∩ T := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact ⟨1, U.one_mem, 1, V.one_mem, by simp [R]⟩
    · exact ⟨1, U.one_mem, 1, W.one_mem, by simp [S]⟩
    · exact ⟨1, U.one_mem, 1, X.one_mem, by simp [T]⟩
  rw [hEmpty] at hone
  exact hone

/-- A four-family cannot contain a triangle with one specified multiplier-one
edge and one specified multiplier-two edge.  The third edge gives Claim 1 or
Claim 2 according to its multiplier. -/
private theorem p43_no_one_two_four
    {G : Type u} [Group G] [Finite G]
    (U V W X : Subgroup G) (a b c d : G) {ru rv rw rx : ℕ}
    (hU : U.index = 3 * ru) (hV : V.index = 3 * rv)
    (hW : W.index = 3 * rw) (hX : X.index = 3 * rx)
    (hruv : Nat.Coprime ru rv) (hruw : Nat.Coprime ru rw)
    (hrux : Nat.Coprime ru rx) (hrvw : Nat.Coprime rv rw)
    (hrvx : Nat.Coprime rv rx) (hrwx : Nat.Coprime rw rx)
    (hrelUV : U.relIndex V = ru)
    (hrelUW : U.relIndex W = 2 * ru)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hUX : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset d X x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x))
    (hVX : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset d X x))
    (hWX : ∀ x, ¬(InLeftCoset c W x ∧ InLeftCoset d X x)) : False := by
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrvpos : 0 < rv := by
    by_contra h
    have : rv = 0 := Nat.eq_zero_of_not_pos h
    exact hVfinite (by simp [hV, this])
  have hVWcases := relIndex_eq_residual_or_twice_of_thrice_coprime
    V W b c hV hW hrvw hVW hVfinite
  rcases hVWcases with hrelVW | hrelVW
  · have hrevWV : W.relIndex V = rw := by
      simpa using (p43_reverse_relIndex_eq_of_thrice_indices V W (c := 1)
        hV hW hrvpos (by simpa using hrelVW))
    exact p43_no_two_one_one_four U W V X a c b d hU hW hV hX
      hruw hruv hrux hrvw.symm hrwx hrvx hrelUW hrelUV hrevWV
      hUW hUV hUX (fun x hx ↦ hVW x ⟨hx.2, hx.1⟩) hWX hVX
  · exact p43_no_one_two_two U V W a b c hU hV hW hruv hruw
      hrvw hrelUV hrelUW hrelVW hUV hUW hVW

/-- Margolis--Schnabel Proposition 4.3 for finite groups.

Four pairwise-disjoint chosen left cosets cannot have subgroup indices
`3 * r i` when the four residuals are pairwise coprime.

The formal proof follows the source's multiplier graph, but makes two repairs
explicit.  First, the mixed `1,2,2` triangle is proved by a parity split rather
than the compressed final inference in the printed Corollary 3.11.  Second,
the all-two case chooses an odd residual as anchor before applying the
double-coset divisibility argument.  Both repairs are proved above from finite
subgroup indices and exact finite-set cardinalities.
-/
theorem margolisSchnabel_prop4_3_finite
    {G : Type u} [Group G] [Finite G]
    (g : Fin 4 → G) (U : Fin 4 → Subgroup G) (r : Fin 4 → ℕ)
    (hindex : ∀ i, (U i).index = 3 * r i)
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
  have hU₀ : U₀.index = 3 * r₀ := by simpa [U₀, r₀] using hindex 0
  have hU₁ : U₁.index = 3 * r₁ := by simpa [U₁, r₁] using hindex 1
  have hU₂ : U₂.index = 3 * r₂ := by simpa [U₂, r₂] using hindex 2
  have hU₃ : U₃.index = 3 * r₃ := by simpa [U₃, r₃] using hindex 3
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
  have hd01 : ∀ x, ¬(InLeftCoset g₀ U₀ x ∧ InLeftCoset g₁ U₁ x) := by
    simpa [g₀, g₁, U₀, U₁] using
      (hharmonic (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide))
  have hd02 : ∀ x, ¬(InLeftCoset g₀ U₀ x ∧ InLeftCoset g₂ U₂ x) := by
    simpa [g₀, g₂, U₀, U₂] using
      (hharmonic (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide))
  have hd03 : ∀ x, ¬(InLeftCoset g₀ U₀ x ∧ InLeftCoset g₃ U₃ x) := by
    simpa [g₀, g₃, U₀, U₃] using
      (hharmonic (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide))
  have hd12 : ∀ x, ¬(InLeftCoset g₁ U₁ x ∧ InLeftCoset g₂ U₂ x) := by
    simpa [g₁, g₂, U₁, U₂] using
      (hharmonic (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide))
  have hd13 : ∀ x, ¬(InLeftCoset g₁ U₁ x ∧ InLeftCoset g₃ U₃ x) := by
    simpa [g₁, g₃, U₁, U₃] using
      (hharmonic (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide))
  have hd23 : ∀ x, ¬(InLeftCoset g₂ U₂ x ∧ InLeftCoset g₃ U₃ x) := by
    simpa [g₂, g₃, U₂, U₃] using
      (hharmonic (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide))
  have hU₀finite : U₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hU₁finite : U₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hU₂finite : U₂.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hU₃finite : U₃.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hr₀pos : 0 < r₀ := by
    by_contra h
    have : r₀ = 0 := Nat.eq_zero_of_not_pos h
    exact hU₀finite (by simp [hU₀, this])
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
  have h01cases := relIndex_eq_residual_or_twice_of_thrice_coprime
    U₀ U₁ g₀ g₁ hU₀ hU₁ hc01 hd01 hU₀finite
  have h02cases := relIndex_eq_residual_or_twice_of_thrice_coprime
    U₀ U₂ g₀ g₂ hU₀ hU₂ hc02 hd02 hU₀finite
  have h03cases := relIndex_eq_residual_or_twice_of_thrice_coprime
    U₀ U₃ g₀ g₃ hU₀ hU₃ hc03 hd03 hU₀finite
  rcases h01cases with h01 | h01
  · have h02 : U₀.relIndex U₂ = r₀ := by
      rcases h02cases with h02 | h02
      · exact h02
      · exact False.elim (p43_no_one_two_four U₀ U₁ U₂ U₃ g₀ g₁ g₂ g₃
          hU₀ hU₁ hU₂ hU₃ hc01 hc02 hc03 hc12 hc13 hc23
          h01 h02 hd01 hd02 hd03 hd12 hd13 hd23)
    have h03 : U₀.relIndex U₃ = r₀ := by
      rcases h03cases with h03 | h03
      · exact h03
      · exact False.elim (p43_no_one_two_four U₀ U₁ U₃ U₂ g₀ g₁ g₃ g₂
          hU₀ hU₁ hU₃ hU₂ hc01 hc03 hc02 hc13 hc12 hc23.symm
          h01 h03 hd01 hd03 hd02 hd13 hd12
          (fun x hx ↦ hd23 x ⟨hx.2, hx.1⟩))
    have h10 : U₁.relIndex U₀ = r₁ := by
      simpa using (p43_reverse_relIndex_eq_of_thrice_indices U₀ U₁ (c := 1)
        hU₀ hU₁ hr₀pos (by simpa using h01))
    have h20 : U₂.relIndex U₀ = r₂ := by
      simpa using (p43_reverse_relIndex_eq_of_thrice_indices U₀ U₂ (c := 1)
        hU₀ hU₂ hr₀pos (by simpa using h02))
    have h30 : U₃.relIndex U₀ = r₃ := by
      simpa using (p43_reverse_relIndex_eq_of_thrice_indices U₀ U₃ (c := 1)
        hU₀ hU₃ hr₀pos (by simpa using h03))
    have hh := p43_harmonic_fin4_of_six g₁ g₂ g₃ g₀ U₁ U₂ U₃ U₀
      hd12 hd13 (fun x hx ↦ hd01 x ⟨hx.2, hx.1⟩) hd23
      (fun x hx ↦ hd02 x ⟨hx.2, hx.1⟩)
      (fun x hx ↦ hd03 x ⟨hx.2, hx.1⟩)
    exact p43_proposition38_three U₁ U₂ U₃ U₀ g₁ g₂ g₃ g₀
      hU₁ hU₂ hU₃ hU₀ hc12 hc13 hc01.symm hc23 hc02.symm hc03.symm
      h10 h20 h30 hh
  · have h02 : U₀.relIndex U₂ = 2 * r₀ := by
      rcases h02cases with h02 | h02
      · exact False.elim (p43_no_one_two_four U₀ U₂ U₁ U₃ g₀ g₂ g₁ g₃
          hU₀ hU₂ hU₁ hU₃ hc02 hc01 hc03 hc12.symm hc23 hc13
          h02 h01 hd02 hd01 hd03 (fun x hx ↦ hd12 x ⟨hx.2, hx.1⟩)
          hd23 hd13)
      · exact h02
    have h03 : U₀.relIndex U₃ = 2 * r₀ := by
      rcases h03cases with h03 | h03
      · exact False.elim (p43_no_one_two_four U₀ U₃ U₁ U₂ g₀ g₃ g₁ g₂
          hU₀ hU₃ hU₁ hU₂ hc03 hc01 hc02 hc13.symm hc23.symm hc12
          h03 h01 hd03 hd01 hd02 (fun x hx ↦ hd13 x ⟨hx.2, hx.1⟩)
          (fun x hx ↦ hd23 x ⟨hx.2, hx.1⟩) hd12)
      · exact h03
    have h10 : U₁.relIndex U₀ = 2 * r₁ :=
      p43_reverse_relIndex_eq_of_thrice_indices U₀ U₁ (c := 2)
        hU₀ hU₁ hr₀pos h01
    have h20 : U₂.relIndex U₀ = 2 * r₂ :=
      p43_reverse_relIndex_eq_of_thrice_indices U₀ U₂ (c := 2)
        hU₀ hU₂ hr₀pos h02
    have h30 : U₃.relIndex U₀ = 2 * r₃ :=
      p43_reverse_relIndex_eq_of_thrice_indices U₀ U₃ (c := 2)
        hU₀ hU₃ hr₀pos h03
    have h12cases := relIndex_eq_residual_or_twice_of_thrice_coprime
      U₁ U₂ g₁ g₂ hU₁ hU₂ hc12 hd12 hU₁finite
    have h13cases := relIndex_eq_residual_or_twice_of_thrice_coprime
      U₁ U₃ g₁ g₃ hU₁ hU₃ hc13 hd13 hU₁finite
    have h23cases := relIndex_eq_residual_or_twice_of_thrice_coprime
      U₂ U₃ g₂ g₃ hU₂ hU₃ hc23 hd23 hU₂finite
    have h12 : U₁.relIndex U₂ = 2 * r₁ := by
      rcases h12cases with h12 | h12
      · exact False.elim (p43_no_one_two_two U₁ U₂ U₀ g₁ g₂ g₀
          hU₁ hU₂ hU₀ hc12 hc01.symm hc02.symm h12 h10 h20
          hd12 (fun x hx ↦ hd01 x ⟨hx.2, hx.1⟩)
          (fun x hx ↦ hd02 x ⟨hx.2, hx.1⟩))
      · exact h12
    have h13 : U₁.relIndex U₃ = 2 * r₁ := by
      rcases h13cases with h13 | h13
      · exact False.elim (p43_no_one_two_two U₁ U₃ U₀ g₁ g₃ g₀
          hU₁ hU₃ hU₀ hc13 hc01.symm hc03.symm h13 h10 h30
          hd13 (fun x hx ↦ hd01 x ⟨hx.2, hx.1⟩)
          (fun x hx ↦ hd03 x ⟨hx.2, hx.1⟩))
      · exact h13
    have h23 : U₂.relIndex U₃ = 2 * r₂ := by
      rcases h23cases with h23 | h23
      · exact False.elim (p43_no_one_two_two U₂ U₃ U₀ g₂ g₃ g₀
          hU₂ hU₃ hU₀ hc23 hc02.symm hc03.symm h23 h20 h30
          hd23 (fun x hx ↦ hd02 x ⟨hx.2, hx.1⟩)
          (fun x hx ↦ hd03 x ⟨hx.2, hx.1⟩))
      · exact h23
    by_cases hr₀Even : Even r₀
    · have hr₁Odd : ¬ Even r₁ := by
        intro hr₁Even
        have htwoGcd : 2 ∣ Nat.gcd r₀ r₁ :=
          Nat.dvd_gcd hr₀Even.two_dvd hr₁Even.two_dvd
        rw [hc01.gcd_eq_one] at htwoGcd
        norm_num at htwoGcd
      exact p43_no_all_two_of_odd_anchor U₁ U₀ U₂ U₃ g₁ g₀ g₂ g₃
        hU₁ hU₀ hU₂ hU₃ hc01.symm hc12 hc13 hc02 hc03 hc23 hr₁Odd
        h10 h12 h13 h02 h03 h23
        (fun x hx ↦ hd01 x ⟨hx.2, hx.1⟩) hd12 hd13 hd02 hd03 hd23
    · exact p43_no_all_two_of_odd_anchor U₀ U₁ U₂ U₃ g₀ g₁ g₂ g₃
        hU₀ hU₁ hU₂ hU₃ hc01 hc02 hc03 hc12 hc13 hc23 hr₀Even
        h01 h02 h03 h12 h13 h23 hd01 hd02 hd03 hd12 hd13 hd23

end ErdosProblems.E274
