import ErdosProblems.E274.FiniteHarmonicCore

/-!
# Margolis--Schnabel Proposition 4.2

An end-to-end finite-group proof of the exact source-shaped obstruction:
three indices `(2*r₁, 2*r₂, 2*r₃)` with pairwise-coprime residuals cannot
be realized by pairwise disjoint chosen left cosets.

The proof follows the source route through its specialized Lemma 4.1 and
Corollary 3.9, whose elementary finite-cardinality content is formalized in
`FiniteHarmonicCore`.
-/

namespace ErdosProblems.E274

open scoped Pointwise

universe u

/-- Margolis--Schnabel Proposition 4.2 for a finite group. -/
theorem margolisSchnabelP42
    {G : Type u} [Group G] [Finite G]
    (U₁ U₂ U₃ : Subgroup G) (g₁ g₂ g₃ : G)
    (r₁ r₂ r₃ : ℕ)
    (h₁ : U₁.index = 2 * r₁)
    (h₂ : U₂.index = 2 * r₂)
    (h₃ : U₃.index = 2 * r₃)
    (h₁₂ : Nat.Coprime r₁ r₂)
    (h₁₃ : Nat.Coprime r₁ r₃)
    (h₂₃ : Nat.Coprime r₂ r₃)
    (hharmonic : IsHarmonicCosetFamily
      ![g₁, g₂, g₃] ![U₁, U₂, U₃]) :
    False := by
  have hdisjoint₁₂ :
      ∀ x, ¬(InLeftCoset g₁ U₁ x ∧ InLeftCoset g₂ U₂ x) := by
    intro x hx
    exact hharmonic (i := 0) (j := 1) (by decide) x (by simpa using hx)
  have hdisjoint₁₃ :
      ∀ x, ¬(InLeftCoset g₁ U₁ x ∧ InLeftCoset g₃ U₃ x) := by
    intro x hx
    exact hharmonic (i := 0) (j := 2) (by decide) x (by simpa using hx)
  have hdisjoint₂₃ :
      ∀ x, ¬(InLeftCoset g₂ U₂ x ∧ InLeftCoset g₃ U₃ x) := by
    intro x hx
    exact hharmonic (i := 1) (j := 2) (by decide) x (by simpa using hx)
  have hleft :
      (U₁ : Set G) * (U₂ : Set G) =
        (U₁ : Set G) * (U₃ : Set G) :=
    subgroup_mul_eq_subgroup_mul_of_twice_pairwise_coprime
      U₁ U₂ U₃ g₁ g₂ g₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
        hdisjoint₁₂ hdisjoint₁₃ hdisjoint₂₃
  have hright :
      (U₂ : Set G) * (U₁ : Set G) =
        (U₃ : Set G) * (U₁ : Set G) :=
    subgroup_mul_right_eq_of_mul_left_eq U₁ U₂ U₃ hleft
  have hhalf₁₃ :
      2 * Nat.card ((U₁ : Set G) * (U₃ : Set G)) = Nat.card G :=
    two_mul_natCard_subgroup_mul_eq
      U₁ U₃ g₁ g₃ h₁ h₃ h₁₃ hdisjoint₁₃
  have hhalf₂₃ :
      2 * Nat.card ((U₂ : Set G) * (U₃ : Set G)) = Nat.card G :=
    two_mul_natCard_subgroup_mul_eq
      U₂ U₃ g₂ g₃ h₂ h₃ h₂₃ hdisjoint₂₃
  exact not_harmonic_three_of_half_products
    U₁ U₂ U₃ g₁ g₂ g₃
      hdisjoint₁₂ hdisjoint₁₃ hdisjoint₂₃
      hright.symm.subset hhalf₁₃ hhalf₂₃

end ErdosProblems.E274
