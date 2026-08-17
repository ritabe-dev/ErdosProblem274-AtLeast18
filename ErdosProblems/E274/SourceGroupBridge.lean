import ErdosProblems.E274.SearchCompleteness

/-!
# Source-import surface for the E274 bounded group reduction

The reduction must be stated for the existence of a bounded counterexample,
not separately at each exact length: the index-two descent decreases the
number of cosets.  This file keeps the source theorem as an explicit
hypothesis and proves only the final local composition.
-/

namespace ErdosProblems.E274

universe u

/-- There is a nontrivial distinct-index coset partition using at most `N`
cosets. -/
def HasBoundedCounterexample (N : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ n ≤ N ∧ HasDistinctIndexCosetPartition.{u} n

/-- Normalized source-import surface.  In the bounded theorem below it is
derived by choosing a counterexample with the fewest cells, descending past
index two directly to the index-two subgroup, sorting the indices, and applying
the four published non-harmonic subtuple propositions. -/
def SourceBoundedGroupBridge (N : ℕ) : Prop :=
  HasBoundedCounterexample.{u} N →
    ∃ xs : List ℕ,
      2 ≤ xs.length ∧ xs.length ≤ N ∧ IsArithmeticCandidate xs

/-- Exact composition of the explicit source hypothesis and a supplied search
completeness proof with the kernel-checked bounded search. -/
theorem erdos274AtMostSixteen_of_sourceBridge_searchComplete
    (hsource : SourceBoundedGroupBridge.{u} 16)
    (hcomplete : SearchComplete) : erdos274AtMostSixteenTarget.{u} := by
  intro n hn₂ hn₁₆ hcounterexample
  have hbounded : HasBoundedCounterexample.{u} 16 :=
    ⟨n, hn₂, hn₁₆, hcounterexample⟩
  rcases hsource hbounded with ⟨xs, hxs₂, hxs₁₆, hcandidate⟩
  exact noArithmeticCandidateAtMostSixteen_of_searchComplete
    hcomplete xs hcandidate hxs₂ hxs₁₆

/-- With arithmetic search completeness now proved locally, the only remaining
hypothesis for the bounded group theorem is the source-side group reduction. -/
theorem erdos274AtMostSixteen_of_sourceBridge
    (hsource : SourceBoundedGroupBridge.{u} 16) :
    erdos274AtMostSixteenTarget.{u} :=
  erdos274AtMostSixteen_of_sourceBridge_searchComplete hsource searchComplete

end ErdosProblems.E274
