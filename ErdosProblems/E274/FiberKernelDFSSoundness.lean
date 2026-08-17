import ErdosProblems.E274.FiberKernelDFSCore
import ErdosProblems.E274.IndexFourFiberMaskBridge
import Mathlib.Data.List.FinRange

/-!
# Soundness of the kernel-reducible E274 fiber DFS

This module connects the declarative ordered mask witness to the small
memo-free depth-first search.  Its main theorem says that every genuine
three-box fiber assignment determines a successful branch of
`kernelFiberDFS4`.  Consequently, a closed kernel proof that the DFS returns
`false` rules out the declarative assignment; no native-evaluation theorem is
needed in this bridge.
-/

namespace ErdosProblems.E274

/-- The constant-time population count agrees with the semantic three-bit
support cardinality on every valid mask. -/
theorem kernelSupportSize3Fast_eq_kernelSupportSize3
    {mask : Nat} (hpos : 1 ≤ mask) (hlt : mask < 8) :
    kernelSupportSize3Fast mask = kernelSupportSize3 mask := by
  interval_cases mask <;>
    decide +kernel

/-- The mask and induced index selected by an ordered declarative witness are
one of the executable choices for that row. -/
theorem OrderedFiberMaskAssignment4.mem_kernelFiberChoices4
    {rows : List Nat} (assignment : OrderedFiberMaskAssignment4 rows)
    (i : Fin rows.length) :
    (assignment.mask i, assignment.induced i) ∈
      kernelFiberChoices4 (rows.get i) := by
  have hsize := kernelSupportSize3Fast_eq_kernelSupportSize3
    (assignment.mask_pos i) (assignment.mask_lt_eight i)
  have hrelation := assignment.index_relation i
  have hmod :
      (rows.get i * kernelSupportSize3Fast (assignment.mask i)) % 4 = 0 := by
    rw [hsize, hrelation]
    omega
  have hquot :
      rows.get i * kernelSupportSize3Fast (assignment.mask i) / 4 =
        assignment.induced i := by
    rw [hsize, hrelation]
    omega
  rw [kernelFiberChoices4, List.mem_filterMap]
  refine ⟨assignment.mask i, List.mem_range'_1.mpr ⟨assignment.mask_pos i, ?_⟩, ?_⟩
  · simpa using assignment.mask_lt_eight i
  · rw [kernelInducedIndex4, if_pos]
    · simpa using hquot
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨assignment.mask_pos i, assignment.mask_lt_eight i⟩, hmod⟩

/-- The initial accumulator divides an iterated least common multiple. -/
theorem kernel_dvd_foldl_lcm_self (a : Nat) (xs : List Nat) :
    a ∣ xs.foldl Nat.lcm a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      exact (Nat.dvd_lcm_left a x).trans (ih (Nat.lcm a x))

/-- Every list member divides the iterated least common multiple. -/
theorem kernel_dvd_foldl_lcm_of_mem {x : Nat} (a : Nat) {xs : List Nat}
    (hx : x ∈ xs) : x ∣ xs.foldl Nat.lcm a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (Nat.dvd_lcm_right a x).trans
          (kernel_dvd_foldl_lcm_self (Nat.lcm a x) ys)
      · exact ih (Nat.lcm a y) hx

/-- Every induced index in an ordered assignment divides the exact common DFS
scale computed from all row choices. -/
theorem OrderedFiberMaskAssignment4.induced_dvd_kernelFiberScale4
    {rows : List Nat} (assignment : OrderedFiberMaskAssignment4 rows)
    (i : Fin rows.length) :
    assignment.induced i ∣ kernelFiberScale4 rows := by
  apply kernel_dvd_foldl_lcm_of_mem 1
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨rows.get i, List.get_mem rows i, ?_⟩
  exact ⟨(assignment.mask i, assignment.induced i),
    assignment.mem_kernelFiberChoices4 i, rfl⟩

/-- One planned labelled column after an ordered prefix has been processed.
The definition mirrors the successful branch of `kernelUpdateFiberColumn`,
but omits its rejection guards. -/
def orderedKernelFiberColumn {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (b : Fin 3) : List (Fin rows.length) → KernelFiberColumn :=
  List.foldl (fun column i =>
    if (assignment.mask i).testBit b then
      (column.1 + scale / assignment.induced i,
        assignment.induced i :: column.2)
    else column) (0, [])

/-- The three planned labelled columns after an ordered prefix. -/
def orderedKernelFiberState {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (processed : List (Fin rows.length)) : KernelFiberState :=
  [orderedKernelFiberColumn assignment scale 0 processed,
    orderedKernelFiberColumn assignment scale 1 processed,
    orderedKernelFiberColumn assignment scale 2 processed]

@[simp] theorem orderedKernelFiberColumn_nil {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (b : Fin 3) :
    orderedKernelFiberColumn assignment scale b [] = (0, []) := rfl

@[simp] theorem orderedKernelFiberState_nil {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat) :
    orderedKernelFiberState assignment scale [] = emptyKernelFiberState := rfl

@[simp] theorem orderedKernelFiberColumn_append_singleton {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (b : Fin 3) (processed : List (Fin rows.length))
    (i : Fin rows.length) :
    orderedKernelFiberColumn assignment scale b (processed ++ [i]) =
      if (assignment.mask i).testBit b then
        ((orderedKernelFiberColumn assignment scale b processed).1 +
            scale / assignment.induced i,
          assignment.induced i ::
            (orderedKernelFiberColumn assignment scale b processed).2)
      else orderedKernelFiberColumn assignment scale b processed := by
  simp [orderedKernelFiberColumn, List.foldl_append]

/-- The planned fill is the sum of the contributions of exactly the processed
rows selecting this column. -/
theorem orderedKernelFiberColumn_fill_eq_sum {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (b : Fin 3) (processed : List (Fin rows.length)) :
    (orderedKernelFiberColumn assignment scale b processed).1 =
      (processed.map fun i =>
        if (assignment.mask i).testBit b then
          scale / assignment.induced i else 0).sum := by
  induction processed using List.reverseRecOn with
  | nil => simp
  | append_singleton processed i ih =>
      by_cases hib : (assignment.mask i).testBit b <;>
        simp [orderedKernelFiberColumn_append_singleton, ih, hib]

/-- Every induced value in a planned seen list came from an earlier row which
selected the same column. -/
theorem mem_orderedKernelFiberColumn_seen {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (b : Fin 3) (processed : List (Fin rows.length)) {old : Nat}
    (hold : old ∈ (orderedKernelFiberColumn assignment scale b processed).2) :
    ∃ i ∈ processed,
      (assignment.mask i).testBit b = true ∧ assignment.induced i = old := by
  induction processed using List.reverseRecOn with
  | nil => simp at hold
  | append_singleton processed i ih =>
      by_cases hib : (assignment.mask i).testBit b
      · rw [orderedKernelFiberColumn_append_singleton, if_pos hib] at hold
        rcases List.mem_cons.mp hold with hold | hold
        · exact ⟨i, by simp, hib, hold.symm⟩
        · rcases ih hold with ⟨j, hj, hjb, hjold⟩
          exact ⟨j, by simp [hj], hjb, hjold⟩
      · rw [orderedKernelFiberColumn_append_singleton, if_neg hib] at hold
        rcases ih hold with ⟨j, hj, hjb, hjold⟩
        exact ⟨j, by simp [hj], hjb, hjold⟩

/-- A duplicate-free prefix cannot exceed the exact total capacity of a
column. -/
theorem orderedKernelFiberColumn_fill_le_scale {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale) (b : Fin 3)
    (processed : List (Fin rows.length)) (hnodup : processed.Nodup) :
    (orderedKernelFiberColumn assignment scale b processed).1 ≤ scale := by
  classical
  rw [orderedKernelFiberColumn_fill_eq_sum]
  rw [← List.sum_toFinset _ hnodup]
  let contribution : Fin rows.length → Nat := fun i =>
    if (assignment.mask i).testBit b then
      scale / assignment.induced i else 0
  change processed.toFinset.sum contribution ≤ scale
  calc
    processed.toFinset.sum contribution ≤ ∑ i, contribution i :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = ∑ i : {i : Fin rows.length //
          (assignment.mask i).testBit b = true},
          scale / assignment.induced i.1 := by
      have hsub := Finset.sum_subtype
        (p := fun i : Fin rows.length =>
          (assignment.mask i).testBit b = true)
        (F := Subtype.fintype (fun i =>
          (assignment.mask i).testBit b = true))
        (s := Finset.univ.filter fun i : Fin rows.length =>
          (assignment.mask i).testBit b = true)
        (by simp)
        (fun i : Fin rows.length => scale / assignment.induced i)
      change (∑ i, if (assignment.mask i).testBit b then
        scale / assignment.induced i else 0) = _
      rw [← Finset.sum_filter]
      exact hsub
    _ = scale := assignment.scaledCapacity scale hdvd b

/-- Exact sufficient conditions for one kernel column update to succeed. -/
theorem kernelUpdateFiberColumn_eq_some_of_valid
    {scale induced fill : Nat} {seen : List Nat}
    (hne : induced ≠ 0) (hdvd : induced ∣ scale)
    (hfill : fill + scale / induced ≤ scale)
    (hgcd : ∀ old ∈ seen, Nat.gcd induced old ≠ 1) :
    kernelUpdateFiberColumn scale induced (fill, seen) =
      some (fill + scale / induced, induced :: seen) := by
  have hmod : scale % induced = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hany :
      seen.any (fun old => decide (Nat.gcd induced old = 1)) = false := by
    rw [List.any_eq_false]
    intro old hold
    simpa only [Bool.not_eq_true] using decide_eq_false (hgcd old hold)
  simp [kernelUpdateFiberColumn, hne, hmod, hfill, hany]

/-- Assemble three successful labelled column updates into the kernel row
transition. -/
theorem kernelUpdateFiberColumns_eq_some_of_three_columns
    {scale mask induced : Nat}
    {c0 c1 c2 c0' c1' c2' : KernelFiberColumn}
    (h0 : (if mask.testBit 0 then
      kernelUpdateFiberColumn scale induced c0 else some c0) = some c0')
    (h1 : (if mask.testBit 1 then
      kernelUpdateFiberColumn scale induced c1 else some c1) = some c1')
    (h2 : (if mask.testBit 2 then
      kernelUpdateFiberColumn scale induced c2 else some c2) = some c2') :
    kernelUpdateFiberColumns scale mask induced 0 [c0, c1, c2] =
      some [c0', c1', c2'] := by
  cases hbit0 : mask.testBit 0 <;>
    cases hbit1 : mask.testBit 1 <;>
      cases hbit2 : mask.testBit 2 <;>
        simp [kernelUpdateFiberColumns, hbit0, hbit1, hbit2]
          at h0 h1 h2 ⊢ <;> simp_all

/-- Feeding the executable choice attached to one new row advances the
planned state by exactly that row. -/
theorem orderedKernelFiberState_step {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale)
    (processed : List (Fin rows.length)) (i : Fin rows.length)
    (hnodup : processed.Nodup) (hnew : i ∉ processed) :
    kernelUpdateFiberColumns scale (assignment.mask i)
        (assignment.induced i) 0
        (orderedKernelFiberState assignment scale processed) =
      some (orderedKernelFiberState assignment scale (processed ++ [i])) := by
  have hnodup' : (processed ++ [i]).Nodup := by
    simpa only [List.concat_eq_append] using hnodup.concat hnew
  have hcolumn (b : Fin 3) :
      (if (assignment.mask i).testBit b then
          kernelUpdateFiberColumn scale (assignment.induced i)
            (orderedKernelFiberColumn assignment scale b processed)
        else some (orderedKernelFiberColumn assignment scale b processed)) =
        some (orderedKernelFiberColumn assignment scale b
          (processed ++ [i])) := by
    by_cases hib : (assignment.mask i).testBit b
    · simp only [if_pos hib]
      rw [orderedKernelFiberColumn_append_singleton, if_pos hib]
      apply kernelUpdateFiberColumn_eq_some_of_valid
      · exact assignment.induced_ne_zero i
      · exact hdvd i
      · simpa [orderedKernelFiberColumn_append_singleton, hib] using
          orderedKernelFiberColumn_fill_le_scale assignment scale hdvd b
            (processed ++ [i]) hnodup'
      · intro old hold
        rcases mem_orderedKernelFiberColumn_seen assignment scale b processed hold with
          ⟨j, hj, hjb, hjold⟩
        have hij : i ≠ j := by
          intro hij
          exact hnew (hij ▸ hj)
        have hg := assignment.sameBoxGcd b i j hij hib hjb
        rw [← hjold]
        omega
    · simp [hib, orderedKernelFiberColumn_append_singleton]
  apply kernelUpdateFiberColumns_eq_some_of_three_columns
  · simpa [orderedKernelFiberState] using hcolumn (0 : Fin 3)
  · simpa [orderedKernelFiberState] using hcolumn (1 : Fin 3)
  · simpa [orderedKernelFiberState] using hcolumn (2 : Fin 3)

/-- After all positions have been processed, one planned column is filled
exactly to the common scale. -/
theorem orderedKernelFiberColumn_full_fill {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale) (b : Fin 3) :
    (orderedKernelFiberColumn assignment scale b
      (List.finRange rows.length)).1 = scale := by
  classical
  rw [orderedKernelFiberColumn_fill_eq_sum]
  rw [← List.sum_toFinset _ (List.nodup_finRange rows.length)]
  rw [List.toFinset_finRange]
  calc
    (∑ i : Fin rows.length,
        if (assignment.mask i).testBit b then
          scale / assignment.induced i else 0) =
        ∑ i : {i : Fin rows.length //
          (assignment.mask i).testBit b = true},
          scale / assignment.induced i.1 := by
      have hsub := Finset.sum_subtype
        (p := fun i : Fin rows.length =>
          (assignment.mask i).testBit b = true)
        (F := Subtype.fintype (fun i =>
          (assignment.mask i).testBit b = true))
        (s := Finset.univ.filter fun i : Fin rows.length =>
          (assignment.mask i).testBit b = true)
        (by simp)
        (fun i : Fin rows.length => scale / assignment.induced i)
      rw [← Finset.sum_filter]
      exact hsub
    _ = scale := assignment.scaledCapacity scale hdvd b

/-- At the terminal planned state all three labelled columns are full. -/
theorem orderedKernelFiberState_terminal {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale) :
    (orderedKernelFiberState assignment scale
      (List.finRange rows.length)).all (fun column => column.1 = scale) = true := by
  simp [orderedKernelFiberState,
    orderedKernelFiberColumn_full_fill assignment scale hdvd]

/-- A complete ordered assignment supplies a successful recursive DFS path.
The two lists partition the canonical ordered list of row positions. -/
theorem orderedKernelFiberDFS_path {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale)
    (processed remaining : List (Fin rows.length))
    (hcomplete : processed ++ remaining = List.finRange rows.length)
    (hnodup : (processed ++ remaining).Nodup) :
    kernelFiberDFS4 scale (remaining.map rows.get)
      (orderedKernelFiberState assignment scale processed) = true := by
  induction remaining generalizing processed with
  | nil =>
      simp only [List.append_nil] at hcomplete
      subst processed
      simpa [kernelFiberDFS4] using
        orderedKernelFiberState_terminal assignment scale hdvd
  | cons i remaining ih =>
      have hprocessed : processed.Nodup := hnodup.of_append_left
      have hnew : i ∉ processed := by
        intro hi
        have hparts := List.nodup_append.mp hnodup
        exact hparts.2.2 i hi i (by simp) rfl
      have hstep := orderedKernelFiberState_step assignment scale hdvd
        processed i hprocessed hnew
      have hchoice := assignment.mem_kernelFiberChoices4 i
      have hcomplete' :
          (processed ++ [i]) ++ remaining = List.finRange rows.length := by
        simpa [List.append_assoc] using hcomplete
      have hnodup' : ((processed ++ [i]) ++ remaining).Nodup := by
        simpa [List.append_assoc] using hnodup
      have htail := ih (processed := processed ++ [i]) hcomplete' hnodup'
      simp only [List.map_cons, kernelFiberDFS4]
      apply List.any_eq_true.mpr
      refine ⟨(assignment.mask i, assignment.induced i), hchoice, ?_⟩
      rw [hstep]
      exact htail

/-- Main DFS completeness theorem: every ordered declarative mask assignment
forces the kernel-reducible search to return `true`. -/
theorem kernelFiberDFS4_complete_of_orderedAssignment {rows : List Nat}
    (assignment : OrderedFiberMaskAssignment4 rows) (scale : Nat)
    (hdvd : ∀ i, assignment.induced i ∣ scale) :
    kernelFiberDFS4 scale rows emptyKernelFiberState = true := by
  have hpath := orderedKernelFiberDFS_path assignment scale hdvd []
    (List.finRange rows.length) (by simp) (List.nodup_finRange rows.length)
  have hrows :
      (List.finRange rows.length).map rows.get = rows := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get rows
  simpa [hrows] using hpath

/-- Scale-specialized form used by the closed profile certificates. -/
theorem kernelFiberDFS4_complete_of_orderedAssignment_fiberScale
    {rows : List Nat} (assignment : OrderedFiberMaskAssignment4 rows) :
    kernelFiberDFS4 (kernelFiberScale4 rows) rows emptyKernelFiberState = true :=
  kernelFiberDFS4_complete_of_orderedAssignment assignment
    (kernelFiberScale4 rows) assignment.induced_dvd_kernelFiberScale4

/-- Direct form used in the five-profile dispatcher: a declarative index-four
assignment on `4 :: rows` forces the tail DFS to succeed. -/
theorem IndexFourFiberAssignment.kernelFiberDFS4_true {rows : List Nat}
    (assignment : IndexFourFiberAssignment (4 :: rows))
    (hnodup : rows.Nodup) (hfour : 4 ∉ rows) :
    kernelFiberDFS4 (kernelFiberScale4 rows) rows emptyKernelFiberState = true :=
  kernelFiberDFS4_complete_of_orderedAssignment_fiberScale
    (assignment.toOrderedMaskAssignment4 hnodup hfour)

end ErdosProblems.E274
