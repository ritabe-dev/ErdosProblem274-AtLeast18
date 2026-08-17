import ErdosProblems.E274.ArithmeticSearchCertificateD0
import ErdosProblems.E274.IndexFourFiberBridge
import ErdosProblems.E274.LocalMargolisSchnabelFacts
import ErdosProblems.E274.SearchCompleteness

/-!
# Closed composition through a kernel fiber obstruction

The earlier composition passed a declarative index-four assignment through an
executable breadth-first search.  For the kernel-only endpoint it is cleaner
to state the remaining finite obligation directly: none of the five exact
length-seventeen profiles admits such a declarative assignment.

This module proves the whole arbitrary-group theorem from that single finite
obligation.  All source-shaped Margolis--Schnabel consequences are supplied by
`localMargolisSchnabelFacts`, and the seventeen-term arithmetic boundary is
supplied by the D0--D17 kernel certificate chain.
-/

namespace ErdosProblems.E274

universe u

/-- Exact remaining finite interface after the group and arithmetic reductions
have been closed locally. -/
def SeventeenIndexFourAssignmentObstruction : Prop :=
  ∀ xs : List Nat, xs ∈ seventeenSurvivors →
    IndexFourFiberAssignment xs → False

/-- Every stored seventeen-term profile contains the unique smallest index
four needed by the direct index-four construction. -/
theorem seventeenSurvivor_mem_four_kernel {xs : List Nat}
    (hmem : xs ∈ seventeenSurvivors) : 4 ∈ xs := by
  simp only [seventeenSurvivors, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> simp

/-- Composition theorem parameterized only by the exact finite
declarative-assignment obstruction; all literature-shaped inputs are already
proved locally. -/
theorem erdos274AtMostSeventeen_of_assignmentObstruction
    (hobstruction : SeventeenIndexFourAssignmentObstruction) :
    erdos274AtMostSeventeenTarget.{u} := by
  intro n hnTwo hnSeventeen hcounterexample
  have hbounded : HasBoundedCounterexample.{u} 17 :=
    ⟨n, hnTwo, hnSeventeen, hcounterexample⟩
  rcases hbounded.existsIndexTwoFreeWitness with
    ⟨m, G, groupG, g, H, hmTwo, hmSeventeen, hpartition, hfinite,
      hinjective, hnotTwo⟩
  letI : Group G := groupG
  let xs := sortedIndexList H hinjective
  have hcandidate : IsArithmeticCandidate xs := by
    refine ⟨sortedIndexList_pairwise_lt H hinjective, ?_, ?_, ?_, ?_⟩
    · exact sortedIndexList_all_gt_two hpartition hmTwo hfinite
        hinjective hnotTwo
    · exact sortedIndexList_pairwise_gcd H hinjective
        (localMargolisSchnabelFacts.lemma2_3c
          hpartition hfinite hinjective)
    · exact sortedIndexList_reciprocalSum H hinjective
        (localMargolisSchnabelFacts.lemma2_3b
          hpartition hfinite hinjective)
    · exact sortedIndexList_noPublishedObstruction
        hpartition hfinite hinjective localMargolisSchnabelFacts
  have hxsTwo : 2 ≤ xs.length := by
    simpa [xs] using hmTwo
  have hxsSeventeen : xs.length ≤ 17 := by
    simpa [xs] using hmSeventeen
  by_cases hxsSixteen : xs.length ≤ 16
  · exact noArithmeticCandidateAtMostSixteen_of_searchComplete
      searchComplete xs hcandidate hxsTwo hxsSixteen
  have hlength : xs.length = 17 := by omega
  have hmem : xs ∈ seventeenSurvivors := by
    have hsearch := searchComplete xs hcandidate
    rw [hlength, checked_seventeen_survivors] at hsearch
    exact hsearch
  have hfour : 4 ∈ xs := seventeenSurvivor_mem_four_kernel hmem
  rcases (mem_sortedIndexList_iff H hinjective 4).mp hfour with ⟨k, hk⟩
  have hdensity : ∑ i : Fin m, (((H i).index : ℚ)⁻¹) = 1 :=
    localMargolisSchnabelFacts.lemma2_3b
      hpartition hfinite hinjective
  have hcap := hpartition.indexFourCapacity_of_density
    hfinite hinjective k hk hdensity
  let assignment : IndexFourFiberAssignment xs :=
    hpartition.indexFourFiberAssignment hfinite hinjective k hk hcap
  exact hobstruction xs hmem assignment

end ErdosProblems.E274
