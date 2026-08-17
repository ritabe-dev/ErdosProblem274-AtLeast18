import Mathlib

/-!
# Erdős Problem #274

The Herzog--Schönheim conjecture says that a nontrivial finite partition of a
group into left cosets of finite-index subgroups cannot have all subgroup
indices distinct.
-/

namespace ErdosProblems.E274

universe u

/-- Membership in the left coset `gH`, written without choosing a set-action
normal form. -/
def InLeftCoset {G : Type u} [Group G] (g : G) (H : Subgroup G) (x : G) : Prop :=
  g⁻¹ * x ∈ H

/-- The indexed left cosets form a set partition of `G`. -/
def IsCosetPartition {G : Type u} [Group G] {n : ℕ}
    (g : Fin n → G) (H : Fin n → Subgroup G) : Prop :=
  ∀ x : G, ∃! i : Fin n, InLeftCoset (g i) (H i) x

/-- A counterexample surface at exactly `n` cosets.  The condition `2 ≤ n`
is kept outside this definition so that the nontriviality boundary is visible
in downstream statements. -/
def HasDistinctIndexCosetPartition (n : ℕ) : Prop :=
  ∃ (G : Type u) (_group : Group G) (g : Fin n → G)
      (H : Fin n → Subgroup G),
    letI := _group
    IsCosetPartition g H ∧
      (∀ i, (H i).index ≠ 0) ∧
      Function.Injective (fun i ↦ (H i).index)

/-- The source-facing bounded partial target produced by the current route.
It is deliberately a proposition, not a claimed theorem. -/
def erdos274AtMostSixteenTarget : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 16 →
    ¬HasDistinctIndexCosetPartition.{u} n

/-- The next bounded target investigated by the index-four fiber route. -/
def erdos274AtMostSeventeenTarget : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 17 →
    ¬HasDistinctIndexCosetPartition.{u} n

/-- The full source conjecture.  This remains open. -/
def erdos274Target : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬HasDistinctIndexCosetPartition.{u} n

theorem erdos274AtMostSixteen_of_full (h : erdos274Target.{u}) :
    erdos274AtMostSixteenTarget.{u} := by
  intro n hn _hn16
  exact h n hn

theorem erdos274AtMostSeventeen_of_full (h : erdos274Target.{u}) :
    erdos274AtMostSeventeenTarget.{u} := by
  intro n hn _hn17
  exact h n hn

end ErdosProblems.E274
