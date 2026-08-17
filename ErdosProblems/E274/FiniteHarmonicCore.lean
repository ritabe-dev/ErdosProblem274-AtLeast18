import ErdosProblems.E274.GroupFiberBasics
import Mathlib.GroupTheory.DoubleCoset

/-!
# Finite group tools for harmonic coset obstructions

Reusable elementary lemmas behind the finite-group arguments in
Margolis--Schnabel Section 3 and Proposition 4.2.  Everything here is proved
locally from Mathlib's subgroup-index and finite-cardinality API.
-/

namespace ErdosProblems.E274

open scoped Pointwise

universe u

/-- Membership of `a⁻¹b` in the subgroup product `UV` produces an
intersection point of the chosen left cosets `aU` and `bV`. -/
theorem leftCosets_intersect_of_inv_mul_mem_mul
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

/-- Disjoint chosen cosets force the corresponding relative representative
to lie outside the product of the two subgroups. -/
theorem inv_mul_notMem_mul_of_disjoint_leftCosets
    {G : Type u} [Group G] (U V : Subgroup G) (a b : G)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    a⁻¹ * b ∉ (U : Set G) * (V : Set G) := by
  intro hmem
  rcases leftCosets_intersect_of_inv_mul_mem_mul U V a b hmem with ⟨x, hx⟩
  exact hdisjoint x hx

/-- If `aU` and `bV` are disjoint and both indices are finite, the shifted
`V`-cell meets strictly fewer than all left `U`-cosets. -/
theorem relIndex_lt_index_of_disjoint_leftCosets
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

/-- For two disjoint finite-index cosets with indices `m*r` and `m*s`, where
the residuals are coprime, the first relative index is `r*k` for a strictly
positive multiplier `k < m`.  This is the division-free form of the
intersection multiplier `α` used throughout Margolis--Schnabel Section 3. -/
theorem exists_relIndex_eq_residual_mul_lt_commonFactor
    {G : Type u} [Group G] (U V : Subgroup G) (a b : G)
    {m r s : ℕ} (hm : 0 < m)
    (hU : U.index = m * r) (hV : V.index = m * s)
    (hcop : Nat.Coprime r s)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUfinite : U.index ≠ 0) :
    ∃ k : ℕ, U.relIndex V = r * k ∧ 0 < k ∧ k < m := by
  have hlt : U.relIndex V < m * r := by
    simpa [hU] using relIndex_lt_index_of_disjoint_leftCosets
      U V a b hUfinite hdisjoint
  have hrelne : U.relIndex V ≠ 0 := by
    intro hzero
    exact hUfinite (U.index_eq_zero_of_relIndex_eq_zero hzero)
  have hdvdInter : U.index ∣ (U ⊓ V).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hdvdRaw : m * r ∣ U.relIndex V * (m * s) := by
    rw [← hinter, hU, hV] at hdvdInter
    exact hdvdInter
  have hdvdM : m * r ∣ m * (U.relIndex V * s) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvdRaw
  have hdr : r ∣ U.relIndex V * s :=
    Nat.dvd_of_mul_dvd_mul_left hm hdvdM
  have hdvd : r ∣ U.relIndex V := hcop.dvd_of_dvd_mul_right hdr
  rcases hdvd with ⟨k, hk⟩
  have hrpos : 0 < r := by
    by_contra hr
    have : r = 0 := Nat.eq_zero_of_not_pos hr
    exact hUfinite (by simp [hU, this])
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    exact hrelne (by simpa [this] using hk)
  have hklt : k < m := by
    rw [hk] at hlt
    nlinarith
  exact ⟨k, hk, hkpos, hklt⟩

/-- The divisibility part of the intersection-multiplier argument, without
the disjoint-coset upper bound.  If two subgroup indices have a common factor
`m` and coprime residuals, the relative index is a positive multiple of the
residual belonging to its first subgroup. -/
theorem exists_relIndex_eq_residual_mul
    {G : Type u} [Group G] (U V : Subgroup G)
    {m r s : ℕ} (hm : 0 < m)
    (hU : U.index = m * r) (hV : V.index = m * s)
    (hcop : Nat.Coprime r s) (hUfinite : U.index ≠ 0) :
    ∃ k : ℕ, U.relIndex V = r * k ∧ 0 < k := by
  have hrelne : U.relIndex V ≠ 0 := by
    intro hzero
    exact hUfinite (U.index_eq_zero_of_relIndex_eq_zero hzero)
  have hdvdInter : U.index ∣ (U ⊓ V).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hdvdRaw : m * r ∣ U.relIndex V * (m * s) := by
    rw [← hinter, hU, hV] at hdvdInter
    exact hdvdInter
  have hdvdM : m * r ∣ m * (U.relIndex V * s) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvdRaw
  have hdr : r ∣ U.relIndex V * s :=
    Nat.dvd_of_mul_dvd_mul_left hm hdvdM
  have hdvd : r ∣ U.relIndex V := hcop.dvd_of_dvd_mul_right hdr
  rcases hdvd with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    exact hrelne (by simpa [this] using hk)
  exact ⟨k, hk, hkpos⟩

/-- Specialized form of Margolis--Schnabel Lemma 4.1: if disjoint cosets
come from subgroups of indices `2*r` and `2*s`, with coprime residuals, then
the relative index of their intersection inside the second subgroup is
exactly `r`. -/
theorem relIndex_eq_residual_of_twice_coprime
    {G : Type u} [Group G] (U V : Subgroup G) (a b : G)
    {r s : ℕ} (hU : U.index = 2 * r) (hV : V.index = 2 * s)
    (hcop : Nat.Coprime r s)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUfinite : U.index ≠ 0) :
    U.relIndex V = r := by
  have hlt : U.relIndex V < 2 * r := by
    simpa [hU] using relIndex_lt_index_of_disjoint_leftCosets
      U V a b hUfinite hdisjoint
  have hrelne : U.relIndex V ≠ 0 := by
    intro hzero
    exact hUfinite (U.index_eq_zero_of_relIndex_eq_zero hzero)
  have hdvdInter : U.index ∣ (U ⊓ V).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : U.relIndex V * V.index = (U ⊓ V).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
  have hdvdRaw : 2 * r ∣ U.relIndex V * (2 * s) := by
    rw [← hinter, hU, hV] at hdvdInter
    exact hdvdInter
  have hdvdTwo : 2 * r ∣ 2 * (U.relIndex V * s) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvdRaw
  have hdr : r ∣ U.relIndex V * s := by
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvdTwo
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
  have hklt : k < 2 := by
    rw [hk] at hlt
    nlinarith
  have : k = 1 := by omega
  calc
    U.relIndex V = r * k := hk
    _ = r := by simp [this]

/-- The finite cardinality of a subgroup product, expressed through the
relative index.  This is Lemma 3.2(2) in a division-free form convenient for
Lean: `|UV| = |V| [U : U ∩ V]`. -/
theorem natCard_subgroup_mul
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

/-- Normalize a product-set cardinality by a common index factor. -/
theorem commonFactor_mul_natCard_subgroup_mul_eq
    {G : Type u} [Group G] [Finite G] (U V : Subgroup G)
    {m s k : ℕ} (hV : V.index = m * s)
    (hrel : V.relIndex U = s * k) :
    m * Nat.card ((U : Set G) * (V : Set G)) = k * Nat.card G := by
  rw [natCard_subgroup_mul, hrel]
  have hcard := V.index_mul_card
  rw [hV] at hcard
  calc
    m * (Nat.card V * (s * k)) = k * ((m * s) * Nat.card V) := by ring
    _ = k * Nat.card G := by rw [hcard]

/-- Rewrite a double coset as a subgroup product followed by a right
translation.  The conjugate is chosen so that
`u * (x*t*x⁻¹) * x = u*x*t`. -/
theorem doubleCoset_eq_mul_conjugate_mul_singleton
    {G : Type u} [Group G] (U T : Subgroup G) (x : G) :
    DoubleCoset.doubleCoset x U T =
      ((U : Set G) *
        ((T.map (MulAut.conj x : G →* G) : Subgroup G) : Set G)) *
          ({x} : Set G) := by
  ext y
  constructor
  · intro hy
    rcases (DoubleCoset.mem_doubleCoset.mp hy) with ⟨u, hu, t, ht, rfl⟩
    refine ⟨u * (x * t * x⁻¹), ?_, x, by simp, ?_⟩
    · refine ⟨u, hu, x * t * x⁻¹, ?_, rfl⟩
      exact ⟨t, ht, by simp [MulAut.conj_apply]⟩
    · simp [mul_assoc]
  · rintro ⟨z, hz, y, hy, hzy⟩
    simp only [Set.mem_singleton_iff] at hy
    subst y
    rcases hz with ⟨u, hu, c, hc, huc⟩
    rcases hc with ⟨t, ht, htc⟩
    change x * t * x⁻¹ = c at htc
    apply DoubleCoset.mem_doubleCoset.mpr
    refine ⟨u, hu, t, ht, ?_⟩
    rw [← hzy, ← huc, ← htc]
    simp [mul_assoc]

/-- Right translation does not change the finite cardinality of a set. -/
theorem ncard_mul_singleton
    {G : Type u} [Group G] (S : Set G) (x : G) :
    (S * ({x} : Set G)).ncard = S.ncard := by
  rw [Set.mul_singleton]
  exact Set.ncard_image_of_injective S (Equiv.mulRight x).injective

/-- Lemma 3.4(1), in the lower-bound form needed below.  A double coset of
subgroups with indices `m*r` and `m*s` and coprime residuals contains at
least a `1/m` fraction of the finite group. -/
theorem natCard_le_commonFactor_mul_ncard_doubleCoset
    {G : Type u} [Group G] [Finite G]
    (U T : Subgroup G) (x : G) {m r s : ℕ}
    (hm : 0 < m) (hU : U.index = m * r) (hT : T.index = m * s)
    (hcop : Nat.Coprime r s) :
    Nat.card G ≤ m * (DoubleCoset.doubleCoset x U T).ncard := by
  let C : Subgroup G := T.map (MulAut.conj x)
  have hC : C.index = m * s := by
    calc
      C.index = T.index := T.index_map_equiv (MulAut.conj x)
      _ = m * s := hT
  have hCfinite : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases exists_relIndex_eq_residual_mul C U hm hC hU hcop.symm hCfinite with
    ⟨k, hk, hkpos⟩
  have hnorm :
      m * Nat.card ((U : Set G) * (C : Set G)) = k * Nat.card G :=
    commonFactor_mul_natCard_subgroup_mul_eq U C hC hk
  have hdouble :
      (DoubleCoset.doubleCoset x U T).ncard =
        ((U : Set G) * (C : Set G)).ncard := by
    rw [doubleCoset_eq_mul_conjugate_mul_singleton]
    exact ncard_mul_singleton ((U : Set G) * (C : Set G)) x
  rw [hdouble]
  have hnorm' :
      m * ((U : Set G) * (C : Set G)).ncard = k * Nat.card G := by
    simpa only [Nat.card_coe_set_eq] using hnorm
  have hkone : 1 ≤ k := hkpos
  calc
    Nat.card G = 1 * Nat.card G := by simp
    _ ≤ k * Nat.card G := Nat.mul_le_mul_right _ hkone
    _ = m * ((U : Set G) * (C : Set G)).ncard := hnorm'.symm

/-- Exact integer multiplier behind the preceding double-coset lower bound.
This is the division-free content of Lemma 3.4(1). -/
theorem exists_commonFactor_mul_ncard_doubleCoset_eq
    {G : Type u} [Group G] [Finite G]
    (U T : Subgroup G) (x : G) {m r s : ℕ}
    (hm : 0 < m) (hU : U.index = m * r) (hT : T.index = m * s)
    (hcop : Nat.Coprime r s) :
    ∃ k : ℕ, 0 < k ∧
      m * (DoubleCoset.doubleCoset x U T).ncard = k * Nat.card G := by
  let C : Subgroup G := T.map (MulAut.conj x)
  have hC : C.index = m * s := by
    calc
      C.index = T.index := T.index_map_equiv (MulAut.conj x)
      _ = m * s := hT
  have hCfinite : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases exists_relIndex_eq_residual_mul C U hm hC hU hcop.symm hCfinite with
    ⟨k, hk, hkpos⟩
  refine ⟨k, hkpos, ?_⟩
  have hnorm :
      m * Nat.card ((U : Set G) * (C : Set G)) = k * Nat.card G :=
    commonFactor_mul_natCard_subgroup_mul_eq U C hC hk
  have hdouble :
      (DoubleCoset.doubleCoset x U T).ncard =
        ((U : Set G) * (C : Set G)).ncard := by
    rw [doubleCoset_eq_mul_conjugate_mul_singleton]
    exact ncard_mul_singleton ((U : Set G) * (C : Set G)) x
  rw [hdouble]
  simpa only [Nat.card_coe_set_eq] using hnorm

/-- Under the hypotheses of the specialized Lemma 4.1, the subgroup product
occupies exactly half of the finite ambient group. -/
theorem two_mul_natCard_subgroup_mul_eq
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) (a b : G) {r s : ℕ}
    (hU : U.index = 2 * r) (hV : V.index = 2 * s)
    (hcop : Nat.Coprime r s)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    2 * Nat.card ((U : Set G) * (V : Set G)) = Nat.card G := by
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : V.relIndex U = s :=
    relIndex_eq_residual_of_twice_coprime V U b a hV hU hcop.symm
      (fun x hx ↦ hdisjoint x ⟨hx.2, hx.1⟩) hVfinite
  rw [natCard_subgroup_mul, hrel]
  have hcard := V.index_mul_card
  rw [hV] at hcard
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcard

/-- The common-product step of Margolis--Schnabel Lemma 3.7, specialized to
the common factor two used by Proposition 4.2.  For three pairwise-disjoint
chosen cosets with pairwise-coprime residual indices, the two products having
the same left factor coincide. -/
theorem subgroup_mul_eq_subgroup_mul_of_twice_pairwise_coprime
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G) {r s t : ℕ}
    (hU : U.index = 2 * r) (hV : V.index = 2 * s)
    (hW : W.index = 2 * t)
    (hrs : Nat.Coprime r s) (hrt : Nat.Coprime r t)
    (hst : Nat.Coprime s t)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x)) :
    (U : Set G) * (V : Set G) = (U : Set G) * (W : Set G) := by
  classical
  let T : Subgroup G := V ⊓ W
  have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hWfinite : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrelVU : V.relIndex U = s :=
    relIndex_eq_residual_of_twice_coprime V U b a hV hU hrs.symm
      (fun x hx ↦ hUV x ⟨hx.2, hx.1⟩) hVfinite
  have hrelWU : W.relIndex U = t :=
    relIndex_eq_residual_of_twice_coprime W U c a hW hU hrt.symm
      (fun x hx ↦ hUW x ⟨hx.2, hx.1⟩) hWfinite
  have hrelWV : W.relIndex V = t :=
    relIndex_eq_residual_of_twice_coprime W V c b hW hV hst.symm
      (fun x hx ↦ hVW x ⟨hx.2, hx.1⟩) hWfinite
  have hTleV : T ≤ V := by exact inf_le_left
  have hTindex : T.index = 2 * (s * t) := by
    calc
      T.index = (W ⊓ V).index := by simp [T, inf_comm]
      _ = W.relIndex V * V.index := by
        simpa [Subgroup.inf_relIndex_right] using
          (Subgroup.relIndex_mul_index
            (H := W ⊓ V) (K := V) inf_le_right).symm
      _ = t * (2 * s) := by rw [hrelWV, hV]
      _ = 2 * (s * t) := by ring
  have hTrelV : T.relIndex V = t := by
    calc
      T.relIndex V = (W ⊓ V).relIndex V := by simp [T, inf_comm]
      _ = W.relIndex V := Subgroup.inf_relIndex_right W V
      _ = t := hrelWV
  have hTcardV : t * Nat.card T = Nat.card V := by
    have hcard := (T.subgroupOf V).index_mul_card
    have hequiv : Nat.card (T.subgroupOf V) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleV).toEquiv
    rw [show (T.subgroupOf V).index = T.relIndex V by rfl,
      hTrelV, hequiv] at hcard
    exact hcard
  have hTintU : T.relIndex U ≠ 0 := by
    intro hzero
    exact (Subgroup.index_ne_zero_of_finite : T.index ≠ 0)
      (T.index_eq_zero_of_relIndex_eq_zero hzero)
  have hTdvd : s * t ∣ T.relIndex U := by
    have hdvdInter : T.index ∣ (T ⊓ U).index :=
      Subgroup.index_dvd_of_le inf_le_left
    have hinter : T.relIndex U * U.index = (T ⊓ U).index := by
      simpa [Subgroup.inf_relIndex_right] using
        (Subgroup.relIndex_mul_index (H := T ⊓ U) (K := U) inf_le_right)
    have hraw : 2 * (s * t) ∣ T.relIndex U * (2 * r) := by
      rw [← hinter, hTindex, hU] at hdvdInter
      exact hdvdInter
    have htwo : 2 * (s * t) ∣ 2 * (T.relIndex U * r) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
    have hcancel : s * t ∣ T.relIndex U * r :=
      Nat.dvd_of_mul_dvd_mul_left (by omega) htwo
    exact (hrs.symm.mul_left hrt.symm).dvd_of_dvd_mul_right hcancel
  have hInnerSubsetUV :
      (U : Set G) * (T : Set G) ⊆ (U : Set G) * (V : Set G) := by
    rintro x ⟨u, hu, z, hz, rfl⟩
    exact ⟨u, hu, z, hTleV hz, rfl⟩
  have hInnerSubsetUW :
      (U : Set G) * (T : Set G) ⊆ (U : Set G) * (W : Set G) := by
    rintro x ⟨u, hu, z, hz, rfl⟩
    exact ⟨u, hu, z, (show T ≤ W from inf_le_right) hz, rfl⟩
  have hOuterLeInner :
      Nat.card ((U : Set G) * (V : Set G)) ≤
        Nat.card ((U : Set G) * (T : Set G)) := by
    rw [natCard_subgroup_mul, natCard_subgroup_mul, hrelVU]
    rcases hTdvd with ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_contra hk0
      have : k = 0 := Nat.eq_zero_of_not_pos hk0
      exact hTintU (by simpa [this] using hk)
    rw [hk]
    rw [← hTcardV]
    have hkone : 1 ≤ k := hkpos
    have hmul := Nat.mul_le_mul_left (Nat.card T * (s * t)) hkone
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hInnerEqUV :
      (U : Set G) * (T : Set G) = (U : Set G) * (V : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hInnerSubsetUV
    simpa only [Nat.card_coe_set_eq] using hOuterLeInner
  have hOuterCards :
      Nat.card ((U : Set G) * (V : Set G)) =
        Nat.card ((U : Set G) * (W : Set G)) := by
    have hhalfUV := two_mul_natCard_subgroup_mul_eq
      U V a b hU hV hrs hUV
    have hhalfUW := two_mul_natCard_subgroup_mul_eq
      U W a c hU hW hrt hUW
    omega
  have hInnerEqUW :
      (U : Set G) * (T : Set G) = (U : Set G) * (W : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hInnerSubsetUW
    have hcardInnerUV := congrArg Set.ncard hInnerEqUV
    have hOuterNcards :
        ((U : Set G) * (V : Set G)).ncard =
          ((U : Set G) * (W : Set G)).ncard := by
      simpa only [Nat.card_coe_set_eq] using hOuterCards
    calc
      ((U : Set G) * (W : Set G)).ncard =
          ((U : Set G) * (V : Set G)).ncard := hOuterNcards.symm
      _ ≤ ((U : Set G) * (T : Set G)).ncard := hcardInnerUV.symm.le
  exact hInnerEqUV.symm.trans hInnerEqUW

/-- Inverting a set-product equality reverses the factors.  This elementary
form avoids introducing a subgroup structure on a product set. -/
theorem subgroup_mul_right_eq_of_mul_left_eq
    {G : Type u} [Group G] (U V W : Subgroup G)
    (h : (U : Set G) * (V : Set G) = (U : Set G) * (W : Set G)) :
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

/-- Inverting a product-set inclusion reverses both factors. -/
theorem subgroup_mul_right_subset_of_mul_left_subset
    {G : Type u} [Group G] (U V W : Subgroup G)
    (h : (U : Set G) * (V : Set G) ⊆
      (U : Set G) * (W : Set G)) :
    (V : Set G) * (U : Set G) ⊆
      (W : Set G) * (U : Set G) := by
  rintro x ⟨v, hv, u, hu, rfl⟩
  have hinv : (u⁻¹ * v⁻¹ : G) ∈ (U : Set G) * (V : Set G) :=
    ⟨u⁻¹, U.inv_mem hu, v⁻¹, V.inv_mem hv, rfl⟩
  rcases h hinv with ⟨u', hu', w, hw, huw⟩
  refine ⟨w⁻¹, W.inv_mem hw, u'⁻¹, U.inv_mem hu', ?_⟩
  change u' * w = u⁻¹ * v⁻¹ at huw
  have := congrArg Inv.inv huw
  simpa [mul_inv_rev] using this

/-- Specialized Lemma 3.5/Corollary 3.6 counting step.  Two disjoint
expanded cells, each occupying half of a finite group, cover the group; the
third representative then forces one of the original cells to intersect it.
-/
theorem not_harmonic_three_of_half_products
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x))
    (hincl : (W : Set G) * (U : Set G) ⊆
      (V : Set G) * (U : Set G))
    (hhalfUW : 2 * Nat.card ((U : Set G) * (W : Set G)) = Nat.card G)
    (hhalfVW : 2 * Nat.card ((V : Set G) * (W : Set G)) = Nat.card G) :
    False := by
  classical
  let A : Set G := a • ((U : Set G) * (W : Set G))
  let B : Set G := b • ((V : Set G) * (W : Set G))
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hxA' : a⁻¹ * x ∈ (U : Set G) * (W : Set G) := by
      change x ∈ a • ((U : Set G) * (W : Set G)) at hxA
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hxA
      change a⁻¹ * x ∈ (U : Set G) * (W : Set G) at hxA
      exact hxA
    have hxB' : b⁻¹ * x ∈ (V : Set G) * (W : Set G) := by
      change x ∈ b • ((V : Set G) * (W : Set G)) at hxB
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hxB
      change b⁻¹ * x ∈ (V : Set G) * (W : Set G) at hxB
      exact hxB
    rcases hxA' with ⟨u, hu, w, hw, huw⟩
    rcases hxB' with ⟨v, hv, w', hw', hvw⟩
    have htail : w' * w⁻¹ * u⁻¹ ∈ (W : Set G) * (U : Set G) := by
      exact ⟨w' * w⁻¹, W.mul_mem hw' (W.inv_mem hw),
        u⁻¹, U.inv_mem hu, rfl⟩
    rcases hincl htail with ⟨v', hv', u', hu', hvu⟩
    change v' * u' = w' * w⁻¹ * u⁻¹ at hvu
    have hrel : b⁻¹ * a ∈ (V : Set G) * (U : Set G) := by
      refine ⟨v * v', V.mul_mem hv hv', u', hu', ?_⟩
      calc
        (v * v') * u' = v * (v' * u') := by simp [mul_assoc]
        _ = v * (w' * w⁻¹ * u⁻¹) := by rw [hvu]
        _ = (b⁻¹ * x) * (a⁻¹ * x)⁻¹ := by
          rw [← hvw, ← huw]
          simp [mul_assoc]
        _ = b⁻¹ * a := by simp [mul_assoc]
    rcases leftCosets_intersect_of_inv_mul_mem_mul V U b a hrel with
      ⟨y, hyV, hyU⟩
    exact hUV y ⟨hyU, hyV⟩
  have hcardA : A.ncard = ((U : Set G) * (W : Set G)).ncard := by
    exact Set.ncard_smul_set a ((U : Set G) * (W : Set G))
  have hcardB : B.ncard = ((V : Set G) * (W : Set G)).ncard := by
    exact Set.ncard_smul_set b ((V : Set G) * (W : Set G))
  have hsum : A.ncard + B.ncard = Nat.card G := by
    rw [hcardA, hcardB]
    simpa only [Nat.card_coe_set_eq] using (by omega :
      Nat.card ((U : Set G) * (W : Set G)) +
        Nat.card ((V : Set G) * (W : Set G)) = Nat.card G)
  have hcover : A ∪ B = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (s := A ∪ B) (t := Set.univ)
      (Set.subset_univ (A ∪ B)) ?_
    rw [Set.ncard_union_eq hAB, hsum]
    simp
  have hc : c ∈ A ∪ B := by rw [hcover]; trivial
  rcases hc with hcA | hcB
  · have hmem : a⁻¹ * c ∈ (U : Set G) * (W : Set G) := by
      change c ∈ a • ((U : Set G) * (W : Set G)) at hcA
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hcA
      change a⁻¹ * c ∈ (U : Set G) * (W : Set G) at hcA
      exact hcA
    rcases leftCosets_intersect_of_inv_mul_mem_mul U W a c hmem with ⟨x, hx⟩
    exact hUW x hx
  · have hmem : b⁻¹ * c ∈ (V : Set G) * (W : Set G) := by
      change c ∈ b • ((V : Set G) * (W : Set G)) at hcB
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hcB
      change b⁻¹ * c ∈ (V : Set G) * (W : Set G) at hcB
      exact hcB
    rcases leftCosets_intersect_of_inv_mul_mem_mul V W b c hmem with ⟨x, hx⟩
    exact hVW x hx

/-- Corollary 3.6 in the cardinal form used by Lemma 4.4.  The two
right-thickened cells are disjoint, but their assumed total cardinality would
cover the finite ambient group; the representative of the anchor cell then
lies in one of them. -/
theorem not_harmonic_three_of_product_cover
    {G : Type u} [Group G] [Finite G]
    (U V W : Subgroup G) (a b c : G)
    (hUV : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x))
    (hUW : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset c W x))
    (hVW : ∀ x, ¬(InLeftCoset b V x ∧ InLeftCoset c W x))
    (hincl : (W : Set G) * (U : Set G) ⊆
      (V : Set G) * (U : Set G))
    (hcover : Nat.card G ≤
      Nat.card ((U : Set G) * (W : Set G)) +
        Nat.card ((V : Set G) * (W : Set G))) :
    False := by
  classical
  let A : Set G := a • ((U : Set G) * (W : Set G))
  let B : Set G := b • ((V : Set G) * (W : Set G))
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hxA' : a⁻¹ * x ∈ (U : Set G) * (W : Set G) := by
      change x ∈ a • ((U : Set G) * (W : Set G)) at hxA
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hxA
      change a⁻¹ * x ∈ (U : Set G) * (W : Set G) at hxA
      exact hxA
    have hxB' : b⁻¹ * x ∈ (V : Set G) * (W : Set G) := by
      change x ∈ b • ((V : Set G) * (W : Set G)) at hxB
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hxB
      change b⁻¹ * x ∈ (V : Set G) * (W : Set G) at hxB
      exact hxB
    rcases hxA' with ⟨u, hu, w, hw, huw⟩
    rcases hxB' with ⟨v, hv, w', hw', hvw⟩
    have htail : w' * w⁻¹ * u⁻¹ ∈ (W : Set G) * (U : Set G) := by
      exact ⟨w' * w⁻¹, W.mul_mem hw' (W.inv_mem hw),
        u⁻¹, U.inv_mem hu, rfl⟩
    rcases hincl htail with ⟨v', hv', u', hu', hvu⟩
    change v' * u' = w' * w⁻¹ * u⁻¹ at hvu
    have hrel : b⁻¹ * a ∈ (V : Set G) * (U : Set G) := by
      refine ⟨v * v', V.mul_mem hv hv', u', hu', ?_⟩
      calc
        (v * v') * u' = v * (v' * u') := by simp [mul_assoc]
        _ = v * (w' * w⁻¹ * u⁻¹) := by rw [hvu]
        _ = (b⁻¹ * x) * (a⁻¹ * x)⁻¹ := by
          rw [← hvw, ← huw]
          simp [mul_assoc]
        _ = b⁻¹ * a := by simp [mul_assoc]
    rcases leftCosets_intersect_of_inv_mul_mem_mul V U b a hrel with
      ⟨y, hyV, hyU⟩
    exact hUV y ⟨hyU, hyV⟩
  have hcardA : A.ncard = ((U : Set G) * (W : Set G)).ncard := by
    exact Set.ncard_smul_set a ((U : Set G) * (W : Set G))
  have hcardB : B.ncard = ((V : Set G) * (W : Set G)).ncard := by
    exact Set.ncard_smul_set b ((V : Set G) * (W : Set G))
  have hupper : A.ncard + B.ncard ≤ Nat.card G := by
    have hsub : A ∪ B ⊆ (Set.univ : Set G) := Set.subset_univ _
    have hncard := Set.ncard_le_ncard hsub (Set.finite_univ)
    rw [Set.ncard_union_eq hAB] at hncard
    simpa using hncard
  have hsum : A.ncard + B.ncard = Nat.card G := by
    rw [hcardA, hcardB]
    have hlower : Nat.card G ≤
        ((U : Set G) * (W : Set G)).ncard +
          ((V : Set G) * (W : Set G)).ncard := by
      simpa only [Nat.card_coe_set_eq] using hcover
    omega
  have hcoverSet : A ∪ B = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (s := A ∪ B) (t := Set.univ)
      (Set.subset_univ (A ∪ B)) ?_
    rw [Set.ncard_union_eq hAB, hsum]
    simp
  have hc : c ∈ A ∪ B := by rw [hcoverSet]; trivial
  rcases hc with hcA | hcB
  · have hmem : a⁻¹ * c ∈ (U : Set G) * (W : Set G) := by
      change c ∈ a • ((U : Set G) * (W : Set G)) at hcA
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hcA
      change a⁻¹ * c ∈ (U : Set G) * (W : Set G) at hcA
      exact hcA
    rcases leftCosets_intersect_of_inv_mul_mem_mul U W a c hmem with ⟨x, hx⟩
    exact hUW x hx
  · have hmem : b⁻¹ * c ∈ (V : Set G) * (W : Set G) := by
      change c ∈ b • ((V : Set G) * (W : Set G)) at hcB
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hcB
      change b⁻¹ * c ∈ (V : Set G) * (W : Set G) at hcB
      exact hcB
    rcases leftCosets_intersect_of_inv_mul_mem_mul V W b c hmem with ⟨x, hx⟩
    exact hVW x hx

end ErdosProblems.E274
