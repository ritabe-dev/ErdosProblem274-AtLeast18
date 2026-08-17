import ErdosProblems.E274.ArithmeticSearch

/-!
# Semantic completeness of the E274 denominator search

This file proves the mathematical invariants used by `searchIndexLists`.
Keeping these lemmas separate from the executable definition avoids rerunning
the length-seventeen split kernel-certificate chain during proof development.
-/

namespace ErdosProblems.E274

/-- Rational reciprocal sum attached to a list of natural denominators. -/
def reciprocalSum (xs : List ℕ) : ℚ :=
  (xs.map (fun x : ℕ ↦ ((x : ℚ)⁻¹))).sum

@[simp] theorem reciprocalSum_nil : reciprocalSum [] = 0 := rfl

@[simp] theorem reciprocalSum_cons (x : ℕ) (xs : List ℕ) :
    reciprocalSum (x :: xs) = (x : ℚ)⁻¹ + reciprocalSum xs := rfl

/-- Every reciprocal of a natural number is nonnegative. -/
theorem reciprocal_nonneg (x : ℕ) : (0 : ℚ) ≤ (x : ℚ)⁻¹ := by
  positivity

/-- The reciprocal sum of a list is nonnegative. -/
theorem reciprocalSum_nonneg (xs : List ℕ) : 0 ≤ reciprocalSum xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [reciprocalSum_cons]
      exact add_nonneg (reciprocal_nonneg x) ih

/-- A nonempty list of positive denominators has positive reciprocal sum. -/
theorem reciprocalSum_pos {x : ℕ} {xs : List ℕ} (hx : 0 < x) :
    0 < reciprocalSum (x :: xs) := by
  rw [reciprocalSum_cons]
  have hinv : (0 : ℚ) < (x : ℚ)⁻¹ := by positivity
  exact add_pos_of_pos_of_nonneg hinv (reciprocalSum_nonneg xs)

/-- If every denominator is at least `d`, the reciprocal sum is at most the
number of terms times `1/d`. -/
theorem reciprocalSum_le_card_nsmul {d : ℕ} (hd : 0 < d) (xs : List ℕ)
    (hbound : ∀ x ∈ xs, d ≤ x) :
    reciprocalSum xs ≤ xs.length • ((d : ℚ)⁻¹) := by
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hdx : d ≤ x := hbound x (by simp)
      have htail : ∀ y ∈ xs, d ≤ y := by
        intro y hy
        exact hbound y (by simp [hy])
      have hinv : (x : ℚ)⁻¹ ≤ (d : ℚ)⁻¹ := by
        simpa [one_div] using
          (one_div_le_one_div_of_le hdq (by exact_mod_cast hdx))
      rw [reciprocalSum_cons]
      calc
        (x : ℚ)⁻¹ + reciprocalSum xs ≤
            (d : ℚ)⁻¹ + xs.length • ((d : ℚ)⁻¹) :=
          add_le_add hinv (ih htail)
        _ = (x :: xs).length • ((d : ℚ)⁻¹) := by
          simp [add_mul, add_comm]

/-- If the full list has no published obstruction, neither does any sublist. -/
theorem containsPublishedObstruction_eq_false_of_sublist {xs ys : List ℕ}
    (hsub : xs.Sublist ys) (hys : containsPublishedObstruction ys = false) :
    containsPublishedObstruction xs = false := by
  cases hxs : containsPublishedObstruction xs with
  | false => rfl
  | true =>
      have := containsPublishedObstruction_eq_true_of_sublist hsub hxs
      simp [hys] at this

/-- For a sorted nonempty suffix whose reciprocal sum is `num/den`, the first
denominator lies in the exact interval enumerated by `searchIndexLists`. -/
theorem head_mem_search_interval {d num den : ℕ} {tail : List ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hd : 0 < d)
    (hsorted : (d :: tail).Pairwise (· < ·))
    (hsum : reciprocalSum (d :: tail) = (num : ℚ) / (den : ℚ)) :
    ceilDiv den num ≤ d ∧
      d ≤ (d :: tail).length * den / num := by
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hdenq : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
  have hheadLe : (d : ℚ)⁻¹ ≤ (num : ℚ) / (den : ℚ) := by
    rw [← hsum, reciprocalSum_cons]
    exact le_add_of_nonneg_right (reciprocalSum_nonneg tail)
  have hdenLe : den ≤ num * d := by
    have hq : (den : ℚ) ≤ (num : ℚ) * (d : ℚ) := by
      have hfrac : (1 : ℚ) / (d : ℚ) ≤ (num : ℚ) / (den : ℚ) := by
        simpa only [one_div] using hheadLe
      have hcross := (div_le_div_iff₀ hdq hdenq).mp hfrac
      simpa using hcross
    exact_mod_cast hq
  have hlower : ceilDiv den num ≤ d := by
    rw [ceilDiv, ← Nat.ceilDiv_eq_add_pred_div]
    exact (ceilDiv_le_iff_le_mul hnum).2 hdenLe
  have hheadBounds : ∀ x ∈ d :: tail, d ≤ x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact ((List.pairwise_cons.mp hsorted).1 x hx).le
  have hsumUpper :
      reciprocalSum (d :: tail) ≤
        (d :: tail).length • ((d : ℚ)⁻¹) := by
    exact reciprocalSum_le_card_nsmul hd (d :: tail) hheadBounds
  have hnumMul : num * d ≤ (d :: tail).length * den := by
    have hq :
        (num : ℚ) * (d : ℚ) ≤ ((d :: tail).length : ℚ) * (den : ℚ) := by
      have hfrac :
          (num : ℚ) / (den : ℚ) ≤
            ((d :: tail).length : ℚ) / (d : ℚ) := by
        rw [← hsum]
        simpa [nsmul_eq_mul, one_div, div_eq_mul_inv, mul_assoc, mul_comm,
          mul_left_comm] using hsumUpper
      exact (div_le_div_iff₀ hdenq hdq).mp hfrac
    exact_mod_cast hq
  refine ⟨hlower, ?_⟩
  exact (Nat.le_div_iff_mul_le hnum).2 (by
    simpa [Nat.mul_comm] using hnumMul)

/-- The numerator is positive whenever a nonempty positive-denominator suffix
represents the current residual fraction. -/
theorem residual_num_pos {x num den : ℕ} {xs : List ℕ}
    (hx : 0 < x)
    (hsum : reciprocalSum (x :: xs) = (num : ℚ) / (den : ℚ)) :
    0 < num := by
  by_contra hnum
  have hnumZero : num = 0 := Nat.eq_zero_of_not_pos hnum
  have hzero : reciprocalSum (x :: xs) = 0 := by
    simpa [hnumZero] using hsum
  exact (ne_of_gt (reciprocalSum_pos hx)) hzero

/-- At a completed branch, a zero reciprocal sum forces the natural residual
numerator to be zero when the denominator is positive. -/
theorem residual_num_eq_zero_of_nil {num den : ℕ} (hden : 0 < den)
    (hsum : reciprocalSum [] = (num : ℚ) / (den : ℚ)) :
    num = 0 := by
  have hdenNe : (den : ℚ) ≠ 0 := by positivity
  have hq : (num : ℚ) = 0 := by
    have : (num : ℚ) / (den : ℚ) = 0 := by simpa using hsum.symm
    exact (div_eq_zero_iff).mp this |>.resolve_right hdenNe
  exact_mod_cast hq

/-- Subtracting the selected reciprocal and reducing numerator and denominator
by their gcd preserves the exact rational residual represented by the tail. -/
theorem reciprocalSum_tail_eq_reduced_residual {d num den : ℕ}
    {tail : List ℕ} (hden : 0 < den) (hd : 0 < d)
    (hsum : reciprocalSum (d :: tail) = (num : ℚ) / (den : ℚ)) :
    let rawNum := num * d - den
    let rawDen := den * d
    let common := Nat.gcd rawNum rawDen
    reciprocalSum tail =
      ((rawNum / common : ℕ) : ℚ) / ((rawDen / common : ℕ) : ℚ) := by
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hdenq : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
  have hheadLe : (d : ℚ)⁻¹ ≤ (num : ℚ) / (den : ℚ) := by
    rw [← hsum, reciprocalSum_cons]
    exact le_add_of_nonneg_right (reciprocalSum_nonneg tail)
  have hdenLe : den ≤ num * d := by
    have hfrac : (1 : ℚ) / (d : ℚ) ≤ (num : ℚ) / (den : ℚ) := by
      simpa only [one_div] using hheadLe
    have hcross := (div_le_div_iff₀ hdq hdenq).mp hfrac
    exact_mod_cast (show (den : ℚ) ≤ (num : ℚ) * (d : ℚ) by simpa using hcross)
  let rawNum := num * d - den
  let rawDen := den * d
  let common := Nat.gcd rawNum rawDen
  have htail :
      reciprocalSum tail = (rawNum : ℚ) / (rawDen : ℚ) := by
    have hsubtract :
        reciprocalSum tail =
          (num : ℚ) / (den : ℚ) - (1 : ℚ) / (d : ℚ) := by
      rw [reciprocalSum_cons] at hsum
      simpa [one_div] using (eq_sub_of_add_eq' hsum)
    rw [hsubtract]
    dsimp [rawNum, rawDen]
    rw [Nat.cast_sub hdenLe]
    simp only [Nat.cast_mul]
    field_simp
  have hreduce :
      (((rawNum / common : ℕ) : ℚ) /
          ((rawDen / common : ℕ) : ℚ)) =
        (rawNum : ℚ) / (rawDen : ℚ) := by
    exact Nat.cast_div_div_div_cancel_right
      (K := ℚ) (Nat.gcd_dvd_right rawNum rawDen)
        (Nat.gcd_dvd_left rawNum rawDen)
  exact htail.trans hreduce.symm

/-- The reduced residual denominator remains positive after every recursive
step. -/
theorem reduced_residual_den_pos {d num den : ℕ}
    (hden : 0 < den) (hd : 0 < d) :
    let rawNum := num * d - den
    let rawDen := den * d
    0 < rawDen / Nat.gcd rawNum rawDen := by
  dsimp
  exact Nat.div_gcd_pos_of_pos_right _ (Nat.mul_pos hden hd)

/-- The newly selected forward prefix is a sublist of the full branch. -/
theorem selectedPrefix_sublist (prefixRev tail : List ℕ) (d : ℕ) :
    (d :: prefixRev).reverse.Sublist (prefixRev.reverse ++ d :: tail) := by
  rw [List.reverse_cons]
  exact (List.Sublist.refl prefixRev.reverse).append (by simp)

/-- Semantic gcd and obstruction conditions force the executable branch guard
to accept the next denominator. -/
theorem admissibleNext_eq_true_of_semantic {prefixRev full : List ℕ} {d : ℕ}
    (hgcd : ∀ old ∈ prefixRev, 1 < Nat.gcd d old)
    (hprefix : (d :: prefixRev).reverse.Sublist full)
    (hobstruction : containsPublishedObstruction full = false) :
    admissibleNext prefixRev d = true := by
  have hall :
      prefixRev.all (fun old ↦ decide (1 < Nat.gcd d old)) = true := by
    rw [List.all_eq_true]
    intro old hold
    exact decide_eq_true (hgcd old hold)
  have hprefixFalse :=
    containsPublishedObstruction_eq_false_of_sublist hprefix hobstruction
  rw [admissibleNext, hall]
  simp only [Bool.true_and, Bool.not_eq_true']
  exact hprefixFalse

/-- Core recursive completeness theorem.  It states that every sorted semantic
suffix satisfying the exact residual, gcd, and obstruction invariants occurs
in the executable depth-first search from the corresponding state. -/
theorem searchIndexLists_complete_aux
    (suffix prefixRev : List ℕ) (num den previous : ℕ)
    (hden : 0 < den)
    (hsorted : suffix.Pairwise (· < ·))
    (hprevious : ∀ x ∈ suffix, previous < x)
    (hgt2 : ∀ x ∈ suffix, 2 < x)
    (hgcdSuffix : suffix.Pairwise (fun x y ↦ 1 < Nat.gcd x y))
    (hgcdCross :
      ∀ old ∈ prefixRev, ∀ x ∈ suffix, 1 < Nat.gcd old x)
    (hobstruction :
      containsPublishedObstruction (prefixRev.reverse ++ suffix) = false)
    (hsum : reciprocalSum suffix = (num : ℚ) / (den : ℚ)) :
    prefixRev.reverse ++ suffix ∈
      searchIndexLists suffix.length num den previous prefixRev := by
  induction suffix generalizing prefixRev num den previous with
  | nil =>
      have hnumZero := residual_num_eq_zero_of_nil hden hsum
      simp [searchIndexLists, hnumZero]
  | cons d tail ih =>
      have hd : 0 < d := lt_trans (by omega) (hgt2 d (by simp))
      have hnum : 0 < num := residual_num_pos hd hsum
      have hinterval := head_mem_search_interval hnum hden hd hsorted hsum
      let lower₀ := max (previous + 1) (ceilDiv den num)
      let lower := if previous = 0 then max 3 lower₀ else lower₀
      let upper := (d :: tail).length * den / num
      have hpreviousD : previous + 1 ≤ d := by
        have := hprevious d (by simp)
        omega
      have hlower₀ : lower₀ ≤ d := by
        exact max_le hpreviousD hinterval.1
      have hthree : 3 ≤ d := by
        have := hgt2 d (by simp)
        omega
      have hlower : lower ≤ d := by
        dsimp [lower]
        split
        · exact max_le hthree hlower₀
        · exact hlower₀
      have hupper : d ≤ upper := by
        simpa [upper] using hinterval.2
      have hdRange : d ∈ List.range' lower (upper + 1 - lower) := by
        rw [List.mem_range'_1]
        refine ⟨hlower, ?_⟩
        rw [Nat.add_sub_of_le (by omega : lower ≤ upper + 1)]
        omega
      have hgcdNext : ∀ old ∈ prefixRev, 1 < Nat.gcd d old := by
        intro old hold
        simpa [Nat.gcd_comm] using
          (hgcdCross old hold d (by simp))
      have hadmissible : admissibleNext prefixRev d = true := by
        apply admissibleNext_eq_true_of_semantic hgcdNext
          (selectedPrefix_sublist prefixRev tail d)
        exact hobstruction
      let rawNum := num * d - den
      let rawDen := den * d
      let common := Nat.gcd rawNum rawDen
      have hdenNext : 0 < rawDen / common := by
        exact reduced_residual_den_pos hden hd
      have hsumTail :
          reciprocalSum tail =
            ((rawNum / common : ℕ) : ℚ) /
              ((rawDen / common : ℕ) : ℚ) := by
        exact reciprocalSum_tail_eq_reduced_residual hden hd hsum
      have hsortedTail := (List.pairwise_cons.mp hsorted).2
      have hpreviousTail : ∀ x ∈ tail, d < x :=
        (List.pairwise_cons.mp hsorted).1
      have hgt2Tail : ∀ x ∈ tail, 2 < x := by
        intro x hx
        exact hgt2 x (by simp [hx])
      have hgcdTail := (List.pairwise_cons.mp hgcdSuffix).2
      have hgcdHead : ∀ x ∈ tail, 1 < Nat.gcd d x :=
        (List.pairwise_cons.mp hgcdSuffix).1
      have hgcdCrossNext :
          ∀ old ∈ d :: prefixRev, ∀ x ∈ tail,
            1 < Nat.gcd old x := by
        intro old hold x hx
        rcases List.mem_cons.mp hold with rfl | hold
        · exact hgcdHead x hx
        · exact hgcdCross old hold x (by simp [hx])
      have hobstructionNext :
          containsPublishedObstruction
              ((d :: prefixRev).reverse ++ tail) = false := by
        simpa [List.reverse_cons, List.append_assoc] using hobstruction
      have hrecursive :
          (d :: prefixRev).reverse ++ tail ∈
            searchIndexLists tail.length (rawNum / common)
              (rawDen / common) d (d :: prefixRev) :=
        ih (d :: prefixRev) (rawNum / common) (rawDen / common) d
          hdenNext hsortedTail hpreviousTail hgt2Tail hgcdTail
          hgcdCrossNext hobstructionNext hsumTail
      rw [List.length_cons, searchIndexLists, if_neg (Nat.ne_of_gt hnum)]
      dsimp only
      rw [List.mem_flatMap]
      refine ⟨d, ?_, ?_⟩
      · simpa [lower, lower₀, upper] using hdRange
      · rw [hadmissible]
        simpa [rawNum, rawDen, common, List.reverse_cons,
          List.append_assoc] using hrecursive

/-- The executable recursion enumerates every semantic arithmetic candidate. -/
theorem searchComplete : SearchComplete := by
  intro xs hcandidate
  rcases hcandidate with
    ⟨hsorted, hgt2, hgcd, hsum, hobstruction⟩
  have hprevious : ∀ x ∈ xs, 0 < x := by
    intro x hx
    exact lt_trans (by omega) (hgt2 x hx)
  have hgcdCross :
      ∀ old ∈ ([] : List ℕ), ∀ x ∈ xs,
        1 < Nat.gcd old x := by simp
  have hsum' : reciprocalSum xs = (1 : ℚ) / (1 : ℚ) := by
    simpa [reciprocalSum] using hsum
  have hmem := searchIndexLists_complete_aux xs [] 1 1 0
    (by norm_num) hsorted hprevious hgt2 hgcd hgcdCross
    (by simpa using hobstruction) hsum'
  simpa [candidateIndexLists] using hmem

/-- Fully closed arithmetic consequence: no semantic candidate has between two
and sixteen terms. -/
theorem noArithmeticCandidateAtMostSixteen (xs : List ℕ)
    (hxs : IsArithmeticCandidate xs) (h₂ : 2 ≤ xs.length)
    (h₁₆ : xs.length ≤ 16) : False :=
  noArithmeticCandidateAtMostSixteen_of_searchComplete
    searchComplete xs hxs h₂ h₁₆

end ErdosProblems.E274
