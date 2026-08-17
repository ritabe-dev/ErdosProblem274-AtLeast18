import ErdosProblems.E274.IndexTwoDescent
import ErdosProblems.E274.SourceGroupBridge

/-!
# A bounded minimal counterexample has no index-two cell

Minimality is taken in the number of cells, not in the order of a finite
quotient.  This avoids a finite-quotient construction for the index-two step:
an index-two cell descends directly to a distinct-index partition with one
fewer cell.
-/

namespace ErdosProblems.E274

universe u

/-- If a bounded counterexample exists, one can choose a counterexample with
the same upper bound whose subgroup indices are all different from two. -/
theorem HasBoundedCounterexample.existsIndexTwoFreeWitness
    {N : ℕ} (hbounded : HasBoundedCounterexample.{u} N) :
    ∃ (n : ℕ) (G : Type u) (groupG : Group G)
      (g : Fin n → G) (H : Fin n → Subgroup G),
      letI := groupG
      2 ≤ n ∧ n ≤ N ∧ IsCosetPartition g H ∧
        (∀ i, (H i).index ≠ 0) ∧
        Function.Injective (fun i ↦ (H i).index) ∧
        ∀ i, (H i).index ≠ 2 := by
  classical
  let P : ℕ → Prop := fun n ↦
    2 ≤ n ∧ n ≤ N ∧ HasDistinctIndexCosetPartition.{u} n
  have hexists : ∃ n, P n := by
    simpa [P, HasBoundedCounterexample] using hbounded
  have hchosen :
      ∃ n, P n ∧ ∀ {m : ℕ}, P m → n ≤ m :=
    ⟨Nat.find hexists, Nat.find_spec hexists, fun hm ↦
      Nat.find_min' hexists hm⟩
  rcases hchosen with ⟨n, hn, hminimal⟩
  rcases hn.2.2 with ⟨G, groupG, g, H, hpartition, hfinite, hinjective⟩
  letI : Group G := groupG
  refine ⟨n, G, groupG, g, H, hn.1, hn.2.1, hpartition, hfinite,
    hinjective, ?_⟩
  intro k hk
  by_cases hnTwo : n = 2
  · subst n
    exact noIndexTwoInTwoCellDistinctPartition hpartition hinjective k hk
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hmTwo : 2 ≤ m := by omega
    have hmBound : m ≤ N := by omega
    have hdescended : HasDistinctIndexCosetPartition.{u} m :=
      HasDistinctIndexCosetPartition_of_descendIndexTwo
        hpartition hfinite hinjective k hk
    have hmin := hminimal ⟨hmTwo, hmBound, hdescended⟩
    omega

end ErdosProblems.E274
