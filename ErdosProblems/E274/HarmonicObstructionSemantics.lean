import ErdosProblems.E274.ArithmeticSearch

/-!
# Semantic witnesses for the four published E274 obstructions

The executable detectors are reflected into explicit witness propositions.
This is the arithmetic-facing half of the later bridge to Margolis--Schnabel
Propositions 4.2, 4.3, 4.5, and 4.7.  No group-theoretic source theorem is
asserted in this file.
-/

namespace ErdosProblems.E274

/-- The Boolean pairwise-coprimality checker exactly reflects
`List.Pairwise Nat.Coprime`. -/
theorem pairwiseCoprime_eq_true_iff (xs : List ℕ) :
    pairwiseCoprime xs = true ↔ xs.Pairwise Nat.Coprime := by
  induction xs with
  | nil => simp [pairwiseCoprime]
  | cons x xs ih =>
      simp [pairwiseCoprime, ih, List.pairwise_cons]

/-- Explicit detector witness for Margolis--Schnabel Proposition 4.2. -/
def HasP42DetectorWitness (xs : List ℕ) : Prop :=
  let halves := (xs.filter (fun x ↦ decide (x % 2 = 0))).map (· / 2)
  ∃ rs : List ℕ,
    rs.Sublist halves ∧ rs.length = 3 ∧ rs.Pairwise Nat.Coprime

/-- Explicit detector witness for Margolis--Schnabel Proposition 4.3. -/
def HasP43DetectorWitness (xs : List ℕ) : Prop :=
  let thirds := (xs.filter (fun x ↦ decide (x % 3 = 0))).map (· / 3)
  ∃ rs : List ℕ,
    rs.Sublist thirds ∧ rs.length = 4 ∧ rs.Pairwise Nat.Coprime

/-- Explicit detector witness for Margolis--Schnabel Proposition 4.5. -/
def HasP45DetectorWitness (xs : List ℕ) : Prop :=
  let twiceOdd := (xs.filter (fun x ↦ decide (x % 4 = 2))).map (· / 2)
  let quarters := (xs.filter (fun x ↦ decide (x % 4 = 0))).map (· / 4)
  ∃ r₁ ∈ twiceOdd, ∃ rs : List ℕ,
    rs.Sublist quarters ∧ rs.length = 3 ∧
      (r₁ :: rs).Pairwise Nat.Coprime

/-- Explicit detector witness for Margolis--Schnabel Proposition 4.7. -/
def HasP47DetectorWitness (xs : List ℕ) : Prop :=
  3 ∈ xs ∧
    let threeOdd :=
      (xs.filter (fun x ↦ decide (x ≠ 3 ∧ x % 6 = 3))).map (· / 3)
    let sixths := (xs.filter (fun x ↦ decide (x % 6 = 0))).map (· / 6)
    ∃ r₂ ∈ threeOdd, ∃ rs : List ℕ,
      rs.Sublist sixths ∧ rs.length = 3 ∧
        (r₂ :: rs).Pairwise Nat.Coprime

theorem containsP42_eq_true_iff_witness (xs : List ℕ) :
    containsP42 xs = true ↔ HasP42DetectorWitness xs := by
  unfold containsP42 HasP42DetectorWitness choose
  rw [List.any_eq_true]
  constructor
  · rintro ⟨rs, hrs, hcoprime⟩
    rw [List.mem_sublistsLen] at hrs
    exact ⟨rs, hrs.1, hrs.2, (pairwiseCoprime_eq_true_iff rs).mp hcoprime⟩
  · rintro ⟨rs, hsub, hlen, hcoprime⟩
    exact ⟨rs, List.mem_sublistsLen.mpr ⟨hsub, hlen⟩,
      (pairwiseCoprime_eq_true_iff rs).mpr hcoprime⟩

theorem containsP43_eq_true_iff_witness (xs : List ℕ) :
    containsP43 xs = true ↔ HasP43DetectorWitness xs := by
  unfold containsP43 HasP43DetectorWitness choose
  rw [List.any_eq_true]
  constructor
  · rintro ⟨rs, hrs, hcoprime⟩
    rw [List.mem_sublistsLen] at hrs
    exact ⟨rs, hrs.1, hrs.2, (pairwiseCoprime_eq_true_iff rs).mp hcoprime⟩
  · rintro ⟨rs, hsub, hlen, hcoprime⟩
    exact ⟨rs, List.mem_sublistsLen.mpr ⟨hsub, hlen⟩,
      (pairwiseCoprime_eq_true_iff rs).mpr hcoprime⟩

theorem containsP45_eq_true_iff_witness (xs : List ℕ) :
    containsP45 xs = true ↔ HasP45DetectorWitness xs := by
  unfold containsP45 HasP45DetectorWitness choose
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r₁, hr₁, hrs⟩
    rw [List.any_eq_true] at hrs
    rcases hrs with ⟨rs, hrs, hcoprime⟩
    rw [List.mem_sublistsLen] at hrs
    exact ⟨r₁, hr₁, rs, hrs.1, hrs.2,
      (pairwiseCoprime_eq_true_iff (r₁ :: rs)).mp hcoprime⟩
  · rintro ⟨r₁, hr₁, rs, hsub, hlen, hcoprime⟩
    refine ⟨r₁, hr₁, ?_⟩
    rw [List.any_eq_true]
    exact ⟨rs, List.mem_sublistsLen.mpr ⟨hsub, hlen⟩,
      (pairwiseCoprime_eq_true_iff (r₁ :: rs)).mpr hcoprime⟩

theorem containsP47_eq_true_iff_witness (xs : List ℕ) :
    containsP47 xs = true ↔ HasP47DetectorWitness xs := by
  by_cases hthree : 3 ∈ xs
  · simp only [containsP47, HasP47DetectorWitness, hthree, if_pos, true_and]
    unfold choose
    rw [List.any_eq_true]
    constructor
    · rintro ⟨r₂, hr₂, hrs⟩
      rw [List.any_eq_true] at hrs
      rcases hrs with ⟨rs, hrs, hcoprime⟩
      rw [List.mem_sublistsLen] at hrs
      exact ⟨r₂, hr₂, rs, hrs.1, hrs.2,
        (pairwiseCoprime_eq_true_iff (r₂ :: rs)).mp hcoprime⟩
    · rintro ⟨r₂, hr₂, rs, hsub, hlen, hcoprime⟩
      refine ⟨r₂, hr₂, ?_⟩
      rw [List.any_eq_true]
      exact ⟨rs, List.mem_sublistsLen.mpr ⟨hsub, hlen⟩,
        (pairwiseCoprime_eq_true_iff (r₂ :: rs)).mpr hcoprime⟩
  · simp [containsP47, HasP47DetectorWitness, hthree]

/-- Membership in a filtered division pool reconstructs the corresponding
multiple in the original index list. -/
theorem scaled_mem_of_mem_divisiblePool {xs : List ℕ} {m r : ℕ}
    (hr : r ∈ (xs.filter (fun x ↦ decide (x % m = 0))).map (· / m)) :
    m * r ∈ xs := by
  rcases List.mem_map.mp hr with ⟨x, hx, rfl⟩
  rw [List.mem_filter] at hx
  rcases hx with ⟨hxmem, hxmod⟩
  have hmod : x % m = 0 := of_decide_eq_true hxmod
  have hscale : m * (x / m) = x := by
    have h := Nat.mod_add_div x m
    omega
  simpa [hscale] using hxmem

/-- The `x % 4 = 2` pool is exactly of the form `2*r` with `r` odd. -/
theorem twiceOddPool_mem_source {xs : List ℕ} {r : ℕ}
    (hr : r ∈ (xs.filter (fun x ↦ decide (x % 4 = 2))).map (· / 2)) :
    2 * r ∈ xs ∧ r % 2 = 1 := by
  rcases List.mem_map.mp hr with ⟨x, hx, rfl⟩
  rw [List.mem_filter] at hx
  rcases hx with ⟨hxmem, hxmod⟩
  have hmod : x % 4 = 2 := of_decide_eq_true hxmod
  have hscale : 2 * (x / 2) = x := by omega
  have hodd : (x / 2) % 2 = 1 := by omega
  exact ⟨by simpa [hscale] using hxmem, hodd⟩

/-- The `x % 6 = 3` pool is exactly of the form `3*r` with `r` odd; the
detector also records that this is not the distinguished index `3`. -/
theorem threeOddPool_mem_source {xs : List ℕ} {r : ℕ}
    (hr : r ∈
      (xs.filter (fun x ↦ decide (x ≠ 3 ∧ x % 6 = 3))).map (· / 3)) :
    3 * r ∈ xs ∧ r % 2 = 1 ∧ r ≠ 1 := by
  rcases List.mem_map.mp hr with ⟨x, hx, rfl⟩
  rw [List.mem_filter] at hx
  rcases hx with ⟨hxmem, hxcond⟩
  have hcond : x ≠ 3 ∧ x % 6 = 3 := of_decide_eq_true hxcond
  have hscale : 3 * (x / 3) = x := by omega
  have hodd : (x / 3) % 2 = 1 := by omega
  have hone : x / 3 ≠ 1 := by omega
  exact ⟨by simpa [hscale] using hxmem, hodd, hone⟩

/-- Source-shaped arithmetic pattern for Proposition 4.2. -/
def HasP42SourcePattern (xs : List ℕ) : Prop :=
  ∃ rs : List ℕ, rs.length = 3 ∧ rs.Pairwise Nat.Coprime ∧
    ∀ r ∈ rs, 2 * r ∈ xs

/-- Source-shaped arithmetic pattern for Proposition 4.3. -/
def HasP43SourcePattern (xs : List ℕ) : Prop :=
  ∃ rs : List ℕ, rs.length = 4 ∧ rs.Pairwise Nat.Coprime ∧
    ∀ r ∈ rs, 3 * r ∈ xs

/-- Source-shaped arithmetic pattern for Proposition 4.5. -/
def HasP45SourcePattern (xs : List ℕ) : Prop :=
  ∃ r₁ : ℕ, ∃ rs : List ℕ,
    r₁ % 2 = 1 ∧ rs.length = 3 ∧
      (r₁ :: rs).Pairwise Nat.Coprime ∧
      2 * r₁ ∈ xs ∧ ∀ r ∈ rs, 4 * r ∈ xs

/-- Source-shaped arithmetic pattern for Proposition 4.7. -/
def HasP47SourcePattern (xs : List ℕ) : Prop :=
  3 ∈ xs ∧ ∃ r₂ : ℕ, ∃ rs : List ℕ,
    r₂ % 2 = 1 ∧ r₂ ≠ 1 ∧ rs.length = 3 ∧
      (r₂ :: rs).Pairwise Nat.Coprime ∧
      3 * r₂ ∈ xs ∧ ∀ r ∈ rs, 6 * r ∈ xs

theorem p42DetectorWitness_to_sourcePattern {xs : List ℕ}
    (h : HasP42DetectorWitness xs) : HasP42SourcePattern xs := by
  rcases h with ⟨rs, hsub, hlen, hcoprime⟩
  refine ⟨rs, hlen, hcoprime, ?_⟩
  intro r hr
  exact scaled_mem_of_mem_divisiblePool (hsub.subset hr)

theorem p43DetectorWitness_to_sourcePattern {xs : List ℕ}
    (h : HasP43DetectorWitness xs) : HasP43SourcePattern xs := by
  rcases h with ⟨rs, hsub, hlen, hcoprime⟩
  refine ⟨rs, hlen, hcoprime, ?_⟩
  intro r hr
  exact scaled_mem_of_mem_divisiblePool (hsub.subset hr)

theorem p45DetectorWitness_to_sourcePattern {xs : List ℕ}
    (h : HasP45DetectorWitness xs) : HasP45SourcePattern xs := by
  rcases h with ⟨r₁, hr₁, rs, hsub, hlen, hcoprime⟩
  have hr₁Source := twiceOddPool_mem_source hr₁
  refine ⟨r₁, rs, hr₁Source.2, hlen, hcoprime, hr₁Source.1, ?_⟩
  intro r hr
  exact scaled_mem_of_mem_divisiblePool (hsub.subset hr)

theorem p47DetectorWitness_to_sourcePattern {xs : List ℕ}
    (h : HasP47DetectorWitness xs) : HasP47SourcePattern xs := by
  rcases h with ⟨hthree, r₂, hr₂, rs, hsub, hlen, hcoprime⟩
  have hr₂Source := threeOddPool_mem_source hr₂
  refine ⟨hthree, r₂, rs, hr₂Source.2.1, hr₂Source.2.2,
    hlen, hcoprime, hr₂Source.1, ?_⟩
  intro r hr
  exact scaled_mem_of_mem_divisiblePool (hsub.subset hr)

theorem containsP42_eq_true_to_sourcePattern {xs : List ℕ}
    (h : containsP42 xs = true) : HasP42SourcePattern xs :=
  p42DetectorWitness_to_sourcePattern
    ((containsP42_eq_true_iff_witness xs).mp h)

theorem containsP43_eq_true_to_sourcePattern {xs : List ℕ}
    (h : containsP43 xs = true) : HasP43SourcePattern xs :=
  p43DetectorWitness_to_sourcePattern
    ((containsP43_eq_true_iff_witness xs).mp h)

theorem containsP45_eq_true_to_sourcePattern {xs : List ℕ}
    (h : containsP45 xs = true) : HasP45SourcePattern xs :=
  p45DetectorWitness_to_sourcePattern
    ((containsP45_eq_true_iff_witness xs).mp h)

theorem containsP47_eq_true_to_sourcePattern {xs : List ℕ}
    (h : containsP47 xs = true) : HasP47SourcePattern xs :=
  p47DetectorWitness_to_sourcePattern
    ((containsP47_eq_true_iff_witness xs).mp h)

end ErdosProblems.E274
