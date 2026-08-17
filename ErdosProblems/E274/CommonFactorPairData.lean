import ErdosProblems.E274.FiniteHarmonicCore

/-!
# Common-factor data for a disjoint pair of cosets

This file packages the intersection multiplier used throughout
Margolis--Schnabel Sections 3--4.  For subgroup indices `m*r` and `m*s` with
coprime residuals, disjoint chosen cosets force one common multiplier
`1 ≤ k < m` in both relative-index orientations.  The product cardinalities
are recorded without division.
-/

namespace ErdosProblems.E274

open scoped Pointwise

universe u

/-- Exact symmetric pair data attached to two disjoint finite-group cosets
whose subgroup indices share a factor `m`.  It is proposition-valued so no
choice of multiplier leaks into later definitions. -/
def CommonFactorPairData
    {G : Type u} [Group G]
    (U V : Subgroup G) (m r s : ℕ) : Prop :=
  ∃ k : ℕ,
    0 < k ∧ k < m ∧
      U.relIndex V = r * k ∧ V.relIndex U = s * k

/-- Construct the common intersection multiplier from disjointness of the
chosen left cosets. -/
theorem commonFactorPairData_of_disjoint
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) (a b : G)
    {m r s : ℕ} (hm : 0 < m)
    (hU : U.index = m * r) (hV : V.index = m * s)
    (hcop : Nat.Coprime r s)
    (hdisjoint : ∀ x, ¬(InLeftCoset a U x ∧ InLeftCoset b V x)) :
    CommonFactorPairData U V m r s := by
  have hUfinite : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hVfinite : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases exists_relIndex_eq_residual_mul_lt_commonFactor
      U V a b hm hU hV hcop hdisjoint hUfinite with
    ⟨k, hk, hkpos, hklt⟩
  rcases exists_relIndex_eq_residual_mul_lt_commonFactor
      V U b a hm hV hU hcop.symm
      (fun x hx ↦ hdisjoint x ⟨hx.2, hx.1⟩) hVfinite with
    ⟨l, hl, hlpos, hllt⟩
  have hrpos : 0 < r := by
    by_contra hr
    have : r = 0 := Nat.eq_zero_of_not_pos hr
    exact hUfinite (by simp [hU, this])
  have hspos : 0 < s := by
    by_contra hs
    have : s = 0 := Nat.eq_zero_of_not_pos hs
    exact hVfinite (by simp [hV, this])
  have hsame : k = l := by
    have hinterLeft : U.relIndex V * V.index = (U ⊓ V).index := by
      simpa [Subgroup.inf_relIndex_right] using
        (Subgroup.relIndex_mul_index (H := U ⊓ V) (K := V) inf_le_right)
    have hinterRight : V.relIndex U * U.index = (U ⊓ V).index := by
      rw [inf_comm]
      simpa [Subgroup.inf_relIndex_right] using
        (Subgroup.relIndex_mul_index (H := V ⊓ U) (K := U) inf_le_right)
    have hmul : (m * (r * s)) * k = (m * (r * s)) * l := by
      calc
        (m * (r * s)) * k = (r * k) * (m * s) := by ring
        _ = U.relIndex V * V.index := by rw [hk, hV]
        _ = (U ⊓ V).index := hinterLeft
        _ = V.relIndex U * U.index := hinterRight.symm
        _ = (s * l) * (m * r) := by rw [hl, hU]
        _ = (m * (r * s)) * l := by ring
    exact Nat.mul_left_cancel (by positivity) hmul
  subst l
  exact ⟨k, hkpos, hklt, hk, hl⟩

/-- Enrich common-factor pair data with the two division-free product-size
identities used in the source's finite-cardinality arguments. -/
theorem CommonFactorPairData.withProductCardinalities
    {G : Type u} [Group G] [Finite G]
    {U V : Subgroup G} {m r s : ℕ}
    (h : CommonFactorPairData U V m r s)
    (hU : U.index = m * r) (hV : V.index = m * s) :
    ∃ k : ℕ,
      0 < k ∧ k < m ∧
      U.relIndex V = r * k ∧ V.relIndex U = s * k ∧
      m * Nat.card ((U : Set G) * (V : Set G)) = k * Nat.card G ∧
      m * Nat.card ((V : Set G) * (U : Set G)) = k * Nat.card G := by
  rcases h with ⟨k, hkpos, hklt, hkUV, hkVU⟩
  refine ⟨k, hkpos, hklt, hkUV, hkVU, ?_, ?_⟩
  · exact commonFactor_mul_natCard_subgroup_mul_eq U V hV hkVU
  · exact commonFactor_mul_natCard_subgroup_mul_eq V U hU hkUV

end ErdosProblems.E274
