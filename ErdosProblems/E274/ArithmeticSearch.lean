import ErdosProblems.E274.Problem

/-!
# Exact bounded arithmetic search for E274

This file defines the exact executable search.  Its kernel-checked branch
certificate for the exact five survivors at seventeen terms is split into
small modules headed by `ArithmeticSearchCertificateD0.lean`.  The file does
not silently identify executable output with the semantic Egyptian-fraction
condition: search completeness is exposed as a separate target below.
-/

namespace ErdosProblems.E274

/-- All `k`-element sublists, preserving order. -/
def choose {α : Type*} (k : ℕ) (xs : List α) : List (List α) :=
  xs.sublistsLen k

/-- A successful Boolean existential test is preserved when its input list is
extended along `List.Sublist`. -/
theorem any_eq_true_of_sublist {α : Type*} {p : α → Bool}
    {xs ys : List α} (hsub : xs.Sublist ys) (hxs : xs.any p = true) :
    ys.any p = true := by
  rcases List.any_eq_true.mp hxs with ⟨x, hx, hpx⟩
  exact List.any_eq_true.mpr ⟨x, hsub.subset hx, hpx⟩

/-- Boolean pairwise coprimality checker. -/
def pairwiseCoprime : List ℕ → Bool
  | [] => true
  | x :: xs => xs.all (fun y ↦ decide (Nat.Coprime x y)) && pairwiseCoprime xs

/-- Margolis--Schnabel Proposition 4.2 pattern. -/
def containsP42 (xs : List ℕ) : Bool :=
  let halves := (xs.filter (fun x ↦ decide (x % 2 = 0))).map (· / 2)
  (choose 3 halves).any pairwiseCoprime

/-- Margolis--Schnabel Proposition 4.3 pattern. -/
def containsP43 (xs : List ℕ) : Bool :=
  let thirds := (xs.filter (fun x ↦ decide (x % 3 = 0))).map (· / 3)
  (choose 4 thirds).any pairwiseCoprime

/-- Margolis--Schnabel Proposition 4.5 pattern. -/
def containsP45 (xs : List ℕ) : Bool :=
  let twiceOdd := (xs.filter (fun x ↦ decide (x % 4 = 2))).map (· / 2)
  let quarters := (xs.filter (fun x ↦ decide (x % 4 = 0))).map (· / 4)
  twiceOdd.any fun r₁ ↦
    (choose 3 quarters).any fun rs ↦ pairwiseCoprime (r₁ :: rs)

/-- Margolis--Schnabel Proposition 4.7 pattern. -/
def containsP47 (xs : List ℕ) : Bool :=
  if 3 ∈ xs then
    let threeOdd :=
      (xs.filter (fun x ↦ decide (x ≠ 3 ∧ x % 6 = 3))).map (· / 3)
    let sixths := (xs.filter (fun x ↦ decide (x % 6 = 0))).map (· / 6)
    threeOdd.any fun r₂ ↦
      (choose 3 sixths).any fun rs ↦ pairwiseCoprime (r₂ :: rs)
  else false

/-- Proposition 4.2 witnesses remain present in every superlist. -/
theorem containsP42_eq_true_of_sublist {xs ys : List ℕ}
    (hsub : xs.Sublist ys) (hxs : containsP42 xs = true) :
    containsP42 ys = true := by
  unfold containsP42 at hxs ⊢
  apply any_eq_true_of_sublist
    (List.sublistsLen_sublist_of_sublist 3 ((hsub.filter _).map _)) hxs

/-- Proposition 4.3 witnesses remain present in every superlist. -/
theorem containsP43_eq_true_of_sublist {xs ys : List ℕ}
    (hsub : xs.Sublist ys) (hxs : containsP43 xs = true) :
    containsP43 ys = true := by
  unfold containsP43 at hxs ⊢
  apply any_eq_true_of_sublist
    (List.sublistsLen_sublist_of_sublist 4 ((hsub.filter _).map _)) hxs

/-- Proposition 4.5 witnesses remain present in every superlist. -/
theorem containsP45_eq_true_of_sublist {xs ys : List ℕ}
    (hsub : xs.Sublist ys) (hxs : containsP45 xs = true) :
    containsP45 ys = true := by
  unfold containsP45 at hxs ⊢
  rcases List.any_eq_true.mp hxs with ⟨r₁, hr₁, hrs⟩
  apply List.any_eq_true.mpr
  refine ⟨r₁, ((hsub.filter _).map _).subset hr₁, ?_⟩
  exact any_eq_true_of_sublist
    (List.sublistsLen_sublist_of_sublist 3 ((hsub.filter _).map _)) hrs

/-- Proposition 4.7 witnesses remain present in every superlist. -/
theorem containsP47_eq_true_of_sublist {xs ys : List ℕ}
    (hsub : xs.Sublist ys) (hxs : containsP47 xs = true) :
    containsP47 ys = true := by
  have hthreeXs : 3 ∈ xs := by
    by_contra hthree
    simp [containsP47, hthree] at hxs
  have hthreeYs : 3 ∈ ys := hsub.subset hthreeXs
  simp only [containsP47, if_pos hthreeXs] at hxs
  simp only [containsP47, if_pos hthreeYs]
  rcases List.any_eq_true.mp hxs with ⟨r₂, hr₂, hrs⟩
  apply List.any_eq_true.mpr
  refine ⟨r₂, ((hsub.filter _).map _).subset hr₂, ?_⟩
  exact any_eq_true_of_sublist
    (List.sublistsLen_sublist_of_sublist 3 ((hsub.filter _).map _)) hrs

/-- A prefix already contains one of the four published non-harmonic index
patterns.  Such a violation cannot be repaired by extending the prefix. -/
def containsPublishedObstruction (xs : List ℕ) : Bool :=
  containsP42 xs || containsP43 xs || containsP45 xs || containsP47 xs

/-- Every published obstruction used by the search is monotone under taking a
superlist.  This justifies pruning a branch as soon as a forbidden subtuple
appears. -/
theorem containsPublishedObstruction_eq_true_of_sublist {xs ys : List ℕ}
    (hsub : xs.Sublist ys) (hxs : containsPublishedObstruction xs = true) :
    containsPublishedObstruction ys = true := by
  unfold containsPublishedObstruction at hxs ⊢
  rw [Bool.or_eq_true] at hxs
  rcases hxs with habc | h47
  · rw [Bool.or_eq_true] at habc
    rcases habc with hab | h45
    · rw [Bool.or_eq_true] at hab
      rcases hab with h42 | h43
      · rw [Bool.or_eq_true]
        left
        rw [Bool.or_eq_true]
        left
        rw [Bool.or_eq_true]
        exact Or.inl (containsP42_eq_true_of_sublist hsub h42)
      · rw [Bool.or_eq_true]
        left
        rw [Bool.or_eq_true]
        left
        rw [Bool.or_eq_true]
        exact Or.inr (containsP43_eq_true_of_sublist hsub h43)
    · rw [Bool.or_eq_true]
      left
      rw [Bool.or_eq_true]
      exact Or.inr (containsP45_eq_true_of_sublist hsub h45)
  · rw [Bool.or_eq_true]
    exact Or.inr (containsP47_eq_true_of_sublist hsub h47)

/-- Exact ceiling division for positive divisors. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- A new denominator respects the pairwise-gcd condition and has not created
a published forbidden subtuple.  `prefixRev` stores the chosen denominators in
reverse order; the obstruction detector is deliberately applied after
reversing back to source order so prefix monotonicity can be used directly in
the semantic completeness proof. -/
def admissibleNext (prefixRev : List ℕ) (d : ℕ) : Bool :=
  prefixRev.all (fun old ↦ decide (1 < Nat.gcd d old)) &&
    !(containsPublishedObstruction (d :: prefixRev).reverse)

/-- Pull a Boolean guard out of a `flatMap`.  The arithmetic branch
certificates use this identity to check only the finite list of admissible
next denominators, while keeping every recursive call opaque until a deeper
certificate rewrites it. -/
theorem flatMap_if_eq_filter_flatMap {α β : Type*}
    (xs : List α) (p : α → Bool) (f : α → List β) :
    (xs.flatMap fun x => if p x then f x else []) =
      (xs.filter p).flatMap f := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.filter_cons]
      split <;> simp_all

/-- Exact depth-first enumeration.  The residual reciprocal sum is `num/den`.
At a node with `left` terms remaining, completeness restricts the next
denominator to

`max (previous+1) (ceil (den/num)) ≤ d ≤ floor (left*den/num)`.

The fraction is reduced after every step to keep the kernel-checked branch
certificates small.
-/
def searchIndexLists : ℕ → ℕ → ℕ → ℕ → List ℕ → List (List ℕ)
  | 0, num, _den, _previous, prefixRev =>
      if num = 0 then [prefixRev.reverse] else []
  | left + 1, num, den, previous, prefixRev =>
      if num = 0 then []
      else
        let lower := max (previous + 1) (ceilDiv den num)
        let lower := if previous = 0 then max 3 lower else lower
        let upper := ((left + 1) * den) / num
        (List.range' lower (upper + 1 - lower)).flatMap fun d ↦
          if admissibleNext prefixRev d then
            let rawNum := num * d - den
            let rawDen := den * d
            let common := Nat.gcd rawNum rawDen
            searchIndexLists left (rawNum / common) (rawDen / common) d
              (d :: prefixRev)
          else []

/-- Candidate lists retained by the exact executable search at length `r`. -/
def candidateIndexLists (r : ℕ) : List (List ℕ) :=
  searchIndexLists r 1 1 0 []

/-- The five exact arithmetic survivors at length `17`.  They are not group
partitions and do not refute the conjecture; they mark the stopping boundary of
the four-obstruction route. -/
def seventeenSurvivors : List (List ℕ) :=
  [ [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320],
    [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320],
    [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160],
    [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120],
    [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96] ]

/-- Semantic arithmetic condition forced by the current group-theoretic
reduction. -/
def IsArithmeticCandidate (xs : List ℕ) : Prop :=
  xs.Pairwise (· < ·) ∧
    (∀ x ∈ xs, 2 < x) ∧
    xs.Pairwise (fun x y ↦ 1 < Nat.gcd x y) ∧
    (xs.map (fun x : ℕ ↦ ((x : ℚ)⁻¹))).sum = 1 ∧
    containsPublishedObstruction xs = false

/-- The semantic bridge target saying that the executable recursion enumerates
every semantic candidate.  It is discharged in `SearchCompleteness.lean`. -/
def SearchComplete : Prop :=
  ∀ xs : List ℕ, IsArithmeticCandidate xs →
    xs ∈ candidateIndexLists xs.length

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The pure kernel reduction evaluates all fifteen bounded search instances.
theorem candidateIndexLists_empty_of_bounds {r : ℕ}
    (h₂ : 2 ≤ r) (h₁₆ : r ≤ 16) : candidateIndexLists r = [] := by
  interval_cases r <;> decide

/-- Once `SearchComplete` is proved, the checked search rules out all semantic
arithmetic candidates of lengths `2` through `16`. -/
theorem noArithmeticCandidateAtMostSixteen_of_searchComplete
    (hcomplete : SearchComplete) (xs : List ℕ)
    (hxs : IsArithmeticCandidate xs) (h₂ : 2 ≤ xs.length)
    (h₁₆ : xs.length ≤ 16) : False := by
  have hmem := hcomplete xs hxs
  have hempty := candidateIndexLists_empty_of_bounds h₂ h₁₆
  rw [hempty] at hmem
  simp at hmem

end ErdosProblems.E274
