import ErdosProblems.E274.GroupFiberBasics
import ErdosProblems.E274.IndexProfile
import ErdosProblems.E274.IndexTwoDescent

/-!
# Group-to-arithmetic bridge for the index-four fiber sieve

An index-four cell leaves three other cosets of its subgroup.  Every other
cell meets a nonempty set of those three fibers.  If its ambient index is
`n`, the number of met fibers is `d`, and the induced subgroup index inside
each met fiber is `e`, then `n * d = 4 * e`.

This file packages the resulting finite assignment independently of the
kernel DFS implementation that later rejects the five surviving profiles.
-/

namespace ErdosProblems.E274

universe u

/-- The distinct non-anchor index values in a sorted profile containing `4`.
Using values rather than list positions makes the group bridge invariant under
the search's later row reordering. -/
abbrev IndexFourFiberRow (xs : List ℕ) : Type :=
  ↥(xs.toFinset.erase 4)

/-- The finite three-fiber data forced by an index-four cell. -/
structure IndexFourFiberAssignment (xs : List ℕ) where
  support : IndexFourFiberRow xs → Finset (Fin 3)
  induced : IndexFourFiberRow xs → ℕ
  support_nonempty : ∀ i, (support i).Nonempty
  induced_ne_zero : ∀ i, induced i ≠ 0
  index_relation :
    ∀ i : IndexFourFiberRow xs,
      (i : ℕ) * (support i).card = 4 * induced i
  capacity :
    ∀ b : Fin 3,
      ∑ i : {i : IndexFourFiberRow xs // b ∈ support i},
          (((induced i.1 : ℚ)⁻¹)) = 1
  sameBoxGcd :
    ∀ b : Fin 3, ∀ i j : IndexFourFiberRow xs,
      i ≠ j → b ∈ support i → b ∈ support j →
        1 < Nat.gcd (induced i) (induced j)

/-- The three non-anchor left cosets of an index-four subgroup, before
choosing labels `0,1,2`. -/
abbrev NonAnchorBoxes {G : Type u} [Group G] (H : Subgroup G) : Type u :=
  {q : G ⧸ H // q ≠ QuotientGroup.mk (1 : G)}

/-- An index-four subgroup has exactly three non-anchor left cosets. -/
theorem card_nonAnchorBoxes_eq_three
    {G : Type u} [Group G] (H : Subgroup G) (hindex : H.index = 4) :
    Nat.card (NonAnchorBoxes H) = 3 := by
  classical
  have hfinite : H.index ≠ 0 := by omega
  letI : Fintype (G ⧸ H) := H.fintypeOfIndexNeZero hfinite
  let q₀ : G ⧸ H := QuotientGroup.mk (1 : G)
  have hcardQ : Fintype.card (G ⧸ H) = 4 := by
    rw [← Nat.card_eq_fintype_card, ← H.index_eq_card, hindex]
  have hcompl := Fintype.card_subtype_compl (fun q : G ⧸ H ↦ q = q₀)
  have hcard : Fintype.card {q : G ⧸ H // q ≠ q₀} = 3 := by
    rw [hcardQ] at hcompl
    simpa using hcompl
  rw [Nat.card_eq_fintype_card]
  exact hcard

/-- A noncanonical labelling of the three non-anchor boxes. -/
noncomputable def nonAnchorBoxesEquivFinThree
    {G : Type u} [Group G] (H : Subgroup G) (hindex : H.index = 4) :
    NonAnchorBoxes H ≃ Fin 3 := by
  classical
  have hfinite : H.index ≠ 0 := by omega
  letI : Fintype (G ⧸ H) := H.fintypeOfIndexNeZero hfinite
  letI : Fintype (NonAnchorBoxes H) := Fintype.ofFinite _
  exact (Fintype.equivFin (NonAnchorBoxes H)).trans
    (finCongr (by
      rw [← Nat.card_eq_fintype_card]
      exact card_nonAnchorBoxes_eq_three H hindex))

/-- A shifted cell disjoint from the anchor cell never maps to the anchor
quotient class. -/
theorem shiftedCellBoxEmbedding_ne_anchor
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hdisjoint : ∀ x, ¬(InLeftCoset 1 H x ∧ InLeftCoset g K x))
    (q : K ⧸ H.subgroupOf K) :
    shiftedCellBoxEmbedding H K g q ≠ QuotientGroup.mk (1 : G) := by
  intro hq
  induction q using QuotientGroup.induction_on with
  | _ k =>
      rw [shiftedCellBoxEmbedding_apply_mk] at hq
      have hHmem : g * (k : G) ∈ H := by
        simpa using QuotientGroup.eq.mp hq.symm
      exact hdisjoint (g * (k : G))
        ⟨by simpa [InLeftCoset] using hHmem, by simp [InLeftCoset]⟩

/-- The quotient classes of a shifted cell embed into the non-anchor boxes. -/
def shiftedCellNonAnchorEmbedding
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hdisjoint : ∀ x, ¬(InLeftCoset 1 H x ∧ InLeftCoset g K x)) :
    K ⧸ H.subgroupOf K ↪ NonAnchorBoxes H where
  toFun q :=
    ⟨shiftedCellBoxEmbedding H K g q,
      shiftedCellBoxEmbedding_ne_anchor H K g hdisjoint q⟩
  inj' := fun {_ _} h ↦
    (shiftedCellBoxEmbedding H K g).injective (congrArg Subtype.val h)

/-- The labelled support of one non-anchor cell. -/
noncomputable def indexFourSupport
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hindex : H.index = 4)
    (hdisjoint : ∀ x, ¬(InLeftCoset 1 H x ∧ InLeftCoset g K x)) :
    Finset (Fin 3) := by
  have hrel : H.relIndex K ≠ 0 := by
    intro hzero
    have := H.index_eq_zero_of_relIndex_eq_zero hzero
    omega
  letI : Fintype (K ⧸ H.subgroupOf K) :=
    (H.subgroupOf K).fintypeOfIndexNeZero hrel
  exact Finset.univ.image
    ((shiftedCellNonAnchorEmbedding H K g hdisjoint).trans
      (nonAnchorBoxesEquivFinThree H hindex).toEmbedding)

/-- The support size is the relative index `[K : H ∩ K]`. -/
@[simp] theorem indexFourSupport_card
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hindex : H.index = 4)
    (hdisjoint : ∀ x, ¬(InLeftCoset 1 H x ∧ InLeftCoset g K x)) :
    (indexFourSupport H K g hindex hdisjoint).card = H.relIndex K := by
  have hrel : H.relIndex K ≠ 0 := by
    intro hzero
    have := H.index_eq_zero_of_relIndex_eq_zero hzero
    omega
  letI : Fintype (K ⧸ H.subgroupOf K) :=
    (H.subgroupOf K).fintypeOfIndexNeZero hrel
  rw [indexFourSupport, Finset.card_image_of_injective _
    (((shiftedCellNonAnchorEmbedding H K g hdisjoint).trans
      (nonAnchorBoxesEquivFinThree H hindex).toEmbedding).injective),
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← (H.subgroupOf K).index_eq_card]
  rfl

/-- Every shifted cell meets at least one non-anchor box. -/
theorem indexFourSupport_nonempty
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hindex : H.index = 4)
    (hdisjoint : ∀ x, ¬(InLeftCoset 1 H x ∧ InLeftCoset g K x)) :
    (indexFourSupport H K g hindex hdisjoint).Nonempty := by
  have hrel : H.relIndex K ≠ 0 := by
    intro hzero
    have := H.index_eq_zero_of_relIndex_eq_zero hzero
    omega
  have hcard := indexFourSupport_card H K g hindex hdisjoint
  apply Finset.card_ne_zero.mp
  simpa only [hcard] using hrel

/-- Membership in the labelled support is represented by a quotient class of
the shifted cell. -/
theorem mem_indexFourSupport_iff_exists
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hindex : H.index = 4)
    (hdisjoint : ∀ x, ¬(InLeftCoset 1 H x ∧ InLeftCoset g K x))
    (b : Fin 3) :
    b ∈ indexFourSupport H K g hindex hdisjoint ↔
      ∃ q : K ⧸ H.subgroupOf K,
        nonAnchorBoxesEquivFinThree H hindex
            (shiftedCellNonAnchorEmbedding H K g hdisjoint q) = b := by
  classical
  have hrel : H.relIndex K ≠ 0 := by
    intro hzero
    have := H.index_eq_zero_of_relIndex_eq_zero hzero
    omega
  letI : Fintype (K ⧸ H.subgroupOf K) :=
    (H.subgroupOf K).fintypeOfIndexNeZero hrel
  simp [indexFourSupport]

/-- A point of a shifted cell supplies the corresponding support membership. -/
theorem mem_indexFourSupport_of_point
    {G : Type u} [Group G] (H K : Subgroup G) (g x : G)
    (hindex : H.index = 4)
    (hdisjoint : ∀ y, ¬(InLeftCoset 1 H y ∧ InLeftCoset g K y))
    (hxcell : InLeftCoset g K x)
    (hxbox : (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk (1 : G)) :
    nonAnchorBoxesEquivFinThree H hindex
        ⟨QuotientGroup.mk x, hxbox⟩ ∈
      indexFourSupport H K g hindex hdisjoint := by
  let kx : K := ⟨g⁻¹ * x, hxcell⟩
  apply (mem_indexFourSupport_iff_exists H K g hindex hdisjoint _).2
  refine ⟨QuotientGroup.mk kx, ?_⟩
  apply congrArg (nonAnchorBoxesEquivFinThree H hindex)
  apply Subtype.ext
  simp [shiftedCellNonAnchorEmbedding, kx]

/-- Conversely, a support membership supplies a point in the shifted cell
whose `H`-box has the prescribed label. -/
theorem exists_point_of_mem_indexFourSupport
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hindex : H.index = 4)
    (hdisjoint : ∀ x, ¬(InLeftCoset 1 H x ∧ InLeftCoset g K x))
    (b : Fin 3) (hb : b ∈ indexFourSupport H K g hindex hdisjoint) :
    ∃ (x : G)
      (hxbox : (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk (1 : G)),
      InLeftCoset g K x ∧
        nonAnchorBoxesEquivFinThree H hindex
            ⟨QuotientGroup.mk x, hxbox⟩ = b := by
  rcases (mem_indexFourSupport_iff_exists H K g hindex hdisjoint b).1 hb with
    ⟨q, hq⟩
  induction q using QuotientGroup.induction_on with
  | _ k =>
      let x : G := g * (k : G)
      have hxbox : (QuotientGroup.mk x : G ⧸ H) ≠
          QuotientGroup.mk (1 : G) := by
        simpa [x] using shiftedCellBoxEmbedding_ne_anchor H K g hdisjoint
          (QuotientGroup.mk k)
      refine ⟨x, hxbox, by simp [x, InLeftCoset], ?_⟩
      simpa [x, shiftedCellNonAnchorEmbedding] using hq

/-- The two ways to compute the index of `H ∩ K` give the fiber equation. -/
theorem index_mul_relIndex_eq_index_mul_relIndex
    {G : Type u} [Group G] (H K : Subgroup G) :
    K.index * H.relIndex K = H.index * K.relIndex H := by
  calc
    K.index * H.relIndex K = (H ⊓ K).index := by
      rw [mul_comm, ← Subgroup.inf_relIndex_right H K]
      exact Subgroup.relIndex_mul_index inf_le_right
    _ = (K ⊓ H).index := by rw [inf_comm]
    _ = H.index * K.relIndex H := by
      rw [mul_comm, ← Subgroup.inf_relIndex_right K H]
      exact (Subgroup.relIndex_mul_index inf_le_right).symm

/-- Recover the unique cell whose subgroup index is the value stored in a
non-anchor row. -/
noncomputable def indexFourCell
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) : Fin n :=
  Classical.choose ((mem_sortedIndexList_iff H hinjective (i : ℕ)).mp (by
    simpa using (Finset.mem_erase.mp i.property).2))

@[simp] theorem indexFourCell_index
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) :
    (H (indexFourCell H hinjective i)).index = (i : ℕ) :=
  Classical.choose_spec
    ((mem_sortedIndexList_iff H hinjective (i : ℕ)).mp (by
      simpa using (Finset.mem_erase.mp i.property).2))

theorem indexFourCell_injective
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index)) :
    Function.Injective (indexFourCell H hinjective) := by
  intro i j hij
  apply Subtype.ext
  have := congrArg (fun k : Fin n ↦ (H k).index) hij
  simpa using this

theorem indexFourCell_ne_anchor
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) :
    indexFourCell H hinjective i ≠ k := by
  intro hik
  have hi4 : (i : ℕ) = 4 := by
    rw [← indexFourCell_index H hinjective i, hik, hk]
  exact (Finset.mem_erase.mp i.property).1 hi4

/-- The non-anchor rows are exactly the cells other than the chosen
index-four anchor. -/
noncomputable def indexFourCellEquiv
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4) :
    IndexFourFiberRow (sortedIndexList H hinjective) ≃ {j : Fin n // j ≠ k} where
  toFun i := ⟨indexFourCell H hinjective i,
    indexFourCell_ne_anchor H hinjective k hk i⟩
  invFun j := ⟨(H j).index, Finset.mem_erase.mpr ⟨by
    intro hj4
    exact j.property (hinjective (hj4.trans hk.symm)), by
      simpa using
        (mem_sortedIndexList_iff H hinjective (H j).index).mpr ⟨j, rfl⟩⟩⟩
  left_inv i := by
    apply Subtype.ext
    exact indexFourCell_index H hinjective i
  right_inv j := by
    apply Subtype.ext
    apply hinjective
    exact indexFourCell_index H hinjective _

/-- If two disjoint ambient cells meet the same `A`-coset, their induced
subgroup indices inside that `A`-coset cannot be coprime. -/
theorem induced_gcd_gt_one_of_disjoint_same_box
    {G : Type u} [Group G] (A K L : Subgroup G) (g h x y : G)
    (hKfinite : K.index ≠ 0)
    (hdisjoint : ∀ z, ¬(InLeftCoset g K z ∧ InLeftCoset h L z))
    (hx : InLeftCoset g K x) (hy : InLeftCoset h L y)
    (hsame : (QuotientGroup.mk x : G ⧸ A) = QuotientGroup.mk y) :
    1 < Nat.gcd (K.relIndex A) (L.relIndex A) := by
  let a : A := ⟨x⁻¹ * y, QuotientGroup.eq.mp hsame⟩
  let KA : Subgroup A := K.subgroupOf A
  let LA : Subgroup A := L.subgroupOf A
  have hKAfinite : KA.index ≠ 0 := by
    change K.relIndex A ≠ 0
    intro hzero
    exact hKfinite (K.index_eq_zero_of_relIndex_eq_zero hzero)
  have hfragmentDisjoint :
      ∀ z : A, ¬(InLeftCoset 1 KA z ∧ InLeftCoset a LA z) := by
    intro z hz
    apply hdisjoint (x * (z : G))
    constructor
    · have hzK : (z : G) ∈ K := by
        simpa [InLeftCoset, KA] using hz.1
      change g⁻¹ * (x * (z : G)) ∈ K
      rw [← mul_assoc]
      exact K.mul_mem hx hzK
    · have hzL : (a⁻¹ * z : A) ∈ LA := hz.2
      change h⁻¹ * (x * (z : G)) ∈ L
      have hyL : h⁻¹ * y ∈ L := hy
      have htail : ((a⁻¹ * z : A) : G) ∈ L := hzL
      convert L.mul_mem hyL htail using 1 <;>
        simp [a, mul_assoc]
  simpa [KA, LA, Subgroup.relIndex] using
    gcd_gt_one_of_disjoint_leftCosets KA LA 1 a hKAfinite
      hfragmentDisjoint

/-- Normalize a partition so that the chosen anchor representative is `1`;
then every other row is disjoint from the anchor cell. -/
theorem IsCosetPartition.indexFourAnchorDisjoint
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) :
    ∀ x, ¬(InLeftCoset 1 (H k) x ∧
      InLeftCoset ((g k)⁻¹ * g (indexFourCell H hinjective i))
        (H (indexFourCell H hinjective i)) x) := by
  let gNorm : Fin n → G := fun j ↦ (g k)⁻¹ * g j
  have hnormalized : IsCosetPartition gNorm H := by
    simpa [gNorm] using hpartition.leftTranslate (g k)⁻¹
  have hne : k ≠ indexFourCell H hinjective i :=
    (indexFourCell_ne_anchor H hinjective k hk i).symm
  intro x hx
  exact hnormalized.isHarmonicCosetFamily hne x (by
    simpa [gNorm] using hx)

/-- The support attached to a row of a normalized distinct-index partition. -/
noncomputable def IsCosetPartition.indexFourSupport
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) : Finset (Fin 3) :=
  ErdosProblems.E274.indexFourSupport
    (H k) (H (indexFourCell H hinjective i))
    ((g k)⁻¹ * g (indexFourCell H hinjective i)) hk
    (hpartition.indexFourAnchorDisjoint hinjective k hk i)

/-- The subgroup index induced by a row inside the anchor subgroup. -/
noncomputable def indexFourInduced
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n)
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) : ℕ :=
  (H (indexFourCell H hinjective i)).relIndex (H k)

theorem IsCosetPartition.indexFourSupport_nonempty
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) :
    (hpartition.indexFourSupport hinjective k hk i).Nonempty :=
  ErdosProblems.E274.indexFourSupport_nonempty
    (H k) (H (indexFourCell H hinjective i))
    ((g k)⁻¹ * g (indexFourCell H hinjective i)) hk
    (hpartition.indexFourAnchorDisjoint hinjective k hk i)

theorem indexFourInduced_ne_zero
    {G : Type u} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n)
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) :
    indexFourInduced H hinjective k i ≠ 0 := by
  intro hzero
  exact hfinite (indexFourCell H hinjective i)
    ((H (indexFourCell H hinjective i)).index_eq_zero_of_relIndex_eq_zero
      hzero)

theorem IsCosetPartition.indexFourIndexRelation
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (i : IndexFourFiberRow (sortedIndexList H hinjective)) :
    (i : ℕ) * (hpartition.indexFourSupport hinjective k hk i).card =
      4 * indexFourInduced H hinjective k i := by
  rw [IsCosetPartition.indexFourSupport,
    ErdosProblems.E274.indexFourSupport_card,
    ← indexFourCell_index H hinjective i, ← hk]
  exact index_mul_relIndex_eq_index_mul_relIndex
    (H k) (H (indexFourCell H hinjective i))

theorem IsCosetPartition.indexFourSameBoxGcd
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (b : Fin 3) (i j : IndexFourFiberRow (sortedIndexList H hinjective))
    (hij : i ≠ j)
    (hib : b ∈ hpartition.indexFourSupport hinjective k hk i)
    (hjb : b ∈ hpartition.indexFourSupport hinjective k hk j) :
    1 < Nat.gcd (indexFourInduced H hinjective k i)
      (indexFourInduced H hinjective k j) := by
  let ci := indexFourCell H hinjective i
  let cj := indexFourCell H hinjective j
  let gi : G := (g k)⁻¹ * g ci
  let gj : G := (g k)⁻¹ * g cj
  have hdi := hpartition.indexFourAnchorDisjoint hinjective k hk i
  have hdj := hpartition.indexFourAnchorDisjoint hinjective k hk j
  change b ∈ ErdosProblems.E274.indexFourSupport
    (H k) (H ci) gi hk hdi at hib
  change b ∈ ErdosProblems.E274.indexFourSupport
    (H k) (H cj) gj hk hdj at hjb
  rcases ErdosProblems.E274.exists_point_of_mem_indexFourSupport
      (H k) (H ci) gi hk hdi b hib with ⟨x, hxbox, hxcell, hxlabel⟩
  rcases ErdosProblems.E274.exists_point_of_mem_indexFourSupport
      (H k) (H cj) gj hk hdj b hjb with ⟨y, hybox, hycell, hylabel⟩
  have hsame : (QuotientGroup.mk x : G ⧸ H k) = QuotientGroup.mk y := by
    have hsub :
        (⟨QuotientGroup.mk x, hxbox⟩ : NonAnchorBoxes (H k)) =
          ⟨QuotientGroup.mk y, hybox⟩ := by
      apply (nonAnchorBoxesEquivFinThree (H k) hk).injective
      exact hxlabel.trans hylabel.symm
    exact congrArg Subtype.val hsub
  have hcij : ci ≠ cj := by
    exact (indexFourCell_injective H hinjective).ne hij
  let gNorm : Fin n → G := fun l ↦ (g k)⁻¹ * g l
  have hnormalized : IsCosetPartition gNorm H := by
    simpa [gNorm] using hpartition.leftTranslate (g k)⁻¹
  have hcellDisjoint :
      ∀ z, ¬(InLeftCoset gi (H ci) z ∧ InLeftCoset gj (H cj) z) := by
    simpa [gi, gj, gNorm] using
      (hnormalized.isHarmonicCosetFamily hcij)
  exact induced_gcd_gt_one_of_disjoint_same_box
    (H k) (H ci) (H cj) gi gj x y (hfinite ci) hcellDisjoint
    hxcell hycell hsame

/-- The finite-measure statement that turns the group bridge into the exact
assignment consumed by the executable sieve.

Mathematically it says that the fragments covering each one of the three
non-anchor `H k`-cosets have reciprocal induced-index sum one.  It is kept as
an explicit proposition so the support, index equation, same-box gcd
obstruction, and finite-cover counting proof have a clear interface. -/
def IsCosetPartition.IndexFourCapacity
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4) : Prop :=
  ∀ b : Fin 3,
    ∑ i : {i : IndexFourFiberRow (sortedIndexList H hinjective) //
        b ∈ hpartition.indexFourSupport hinjective k hk i},
      (((indexFourInduced H hinjective k i.1 : ℚ)⁻¹)) = 1

/-- A distinct-index coset partition with an index-four anchor supplies the
complete finite fiber assignment, conditional only on the explicitly isolated
per-box capacity identity. -/
noncomputable def IsCosetPartition.indexFourFiberAssignment
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (hcapacity : hpartition.IndexFourCapacity hinjective k hk) :
    IndexFourFiberAssignment (sortedIndexList H hinjective) where
  support := hpartition.indexFourSupport hinjective k hk
  induced := indexFourInduced H hinjective k
  support_nonempty :=
    hpartition.indexFourSupport_nonempty hinjective k hk
  induced_ne_zero := indexFourInduced_ne_zero H hfinite hinjective k
  index_relation := hpartition.indexFourIndexRelation hinjective k hk
  capacity := hcapacity
  sameBoxGcd := fun b i j hij hib hjb ↦
    hpartition.indexFourSameBoxGcd hfinite hinjective k hk b i j hij hib hjb

open scoped Pointwise

set_option maxHeartbeats 800000 in
-- Constructing the exact fragment cover requires a longer elaboration budget.
/-- Every non-anchor box receives total reciprocal induced-index mass at
least one. -/
theorem IsCosetPartition.one_le_indexFourCapacity
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (_hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (b : Fin 3) :
    1 ≤ ∑ i : {i : IndexFourFiberRow (sortedIndexList H hinjective) //
        b ∈ hpartition.indexFourSupport hinjective k hk i},
      (((indexFourInduced H hinjective k i.1 : ℚ)⁻¹)) := by
  classical
  let Row := IndexFourFiberRow (sortedIndexList H hinjective)
  let Inc := {i : Row //
    b ∈ hpartition.indexFourSupport hinjective k hk i}
  let A : Subgroup G := H k
  let cell : Inc → Fin n := fun i ↦ indexFourCell H hinjective i.1
  let rep : Inc → G := fun i ↦ (g k)⁻¹ * g (cell i)
  have hdisjoint (i : Inc) :
      ∀ x, ¬(InLeftCoset 1 A x ∧ InLeftCoset (rep i) (H (cell i)) x) := by
    simpa [A, rep, cell] using
      hpartition.indexFourAnchorDisjoint hinjective k hk i.1
  have hpoint : ∀ i : Inc,
      ∃ (x : G)
        (hxbox : (QuotientGroup.mk x : G ⧸ A) ≠ QuotientGroup.mk (1 : G)),
        InLeftCoset (rep i) (H (cell i)) x ∧
          nonAnchorBoxesEquivFinThree A (by simpa [A] using hk)
              ⟨QuotientGroup.mk x, hxbox⟩ = b := by
    intro i
    exact exists_point_of_mem_indexFourSupport
      A (H (cell i)) (rep i) (by simpa [A] using hk) (hdisjoint i) b
      (by simpa [Inc, Row, A, cell, rep,
        IsCosetPartition.indexFourSupport] using i.property)
  choose point pointBox pointCell pointLabel using hpoint
  let box : NonAnchorBoxes A :=
    (nonAnchorBoxesEquivFinThree A (by simpa [A] using hk)).symm b
  let a : G := (box : G ⧸ A).out
  have haBox : (QuotientGroup.mk a : G ⧸ A) = box := by
    exact Quotient.out_eq' _
  have hpointBox (i : Inc) :
      (QuotientGroup.mk a : G ⧸ A) = QuotientGroup.mk (point i) := by
    rw [haBox]
    have hsub :
        (⟨QuotientGroup.mk (point i), pointBox i⟩ : NonAnchorBoxes A) = box := by
      apply (nonAnchorBoxesEquivFinThree A (by simpa [A] using hk)).injective
      simpa [box] using pointLabel i
    exact (congrArg Subtype.val hsub).symm
  let fiberRep : Inc → A := fun i ↦
    ⟨a⁻¹ * point i, QuotientGroup.eq.mp (hpointBox i)⟩
  let fiberSubgroup : Inc → Subgroup A := fun i ↦
    (H (cell i)).subgroupOf A
  have hnormalized : IsCosetPartition (fun j ↦ (g k)⁻¹ * g j) H := by
    simpa using hpartition.leftTranslate (g k)⁻¹
  have hcover :
      ⋃ i ∈ (Finset.univ : Finset Inc),
          (fiberRep i) • (fiberSubgroup i : Set A) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    let x : G := a * (z : G)
    rcases hnormalized x with ⟨j, hj, _hunique⟩
    have hjk : j ≠ k := by
      intro hjk
      subst j
      have hxA : x ∈ A := by
        simpa [A, InLeftCoset] using hj
      have haA : a ∈ A := by
        have hzInv : ((z : G)⁻¹) ∈ A := A.inv_mem z.property
        have hmem := A.mul_mem hxA hzInv
        simpa [x, mul_assoc] using hmem
      have haAnchor :
          (QuotientGroup.mk a : G ⧸ A) = QuotientGroup.mk (1 : G) := by
        rw [QuotientGroup.eq]
        simpa using haA
      exact box.property (haBox.symm.trans haAnchor)
    have hjIndexNe : (H j).index ≠ 4 := by
      intro hj4
      exact hjk (hinjective (hj4.trans hk.symm))
    have hjMem : (H j).index ∈ sortedIndexList H hinjective :=
      (mem_sortedIndexList_iff H hinjective (H j).index).mpr ⟨j, rfl⟩
    let r : Row := ⟨(H j).index,
      Finset.mem_erase.mpr ⟨hjIndexNe, by simpa [Row] using hjMem⟩⟩
    have hcellr : indexFourCell H hinjective r = j := by
      apply hinjective
      exact indexFourCell_index H hinjective r
    have hxbox :
        (QuotientGroup.mk x : G ⧸ A) ≠ QuotientGroup.mk (1 : G) := by
      have hxq : (QuotientGroup.mk x : G ⧸ A) = QuotientGroup.mk a := by
        rw [QuotientGroup.eq]
        simpa [x] using z.property
      exact fun hxone ↦ box.property (haBox.symm.trans (hxq.symm.trans hxone))
    have hxLabel :
        nonAnchorBoxesEquivFinThree A (by simpa [A] using hk)
          ⟨QuotientGroup.mk x, hxbox⟩ = b := by
      rw [← show nonAnchorBoxesEquivFinThree A
          (by simpa [A] using hk) box = b by simp [box]]
      apply congrArg
        (nonAnchorBoxesEquivFinThree A (by simpa [A] using hk))
      apply Subtype.ext
      change (QuotientGroup.mk x : G ⧸ A) = box
      have hxq : (QuotientGroup.mk x : G ⧸ A) = QuotientGroup.mk a := by
        rw [QuotientGroup.eq]
        simpa [x] using z.property
      exact hxq.trans haBox
    have hxCell :
        InLeftCoset ((g k)⁻¹ * g (indexFourCell H hinjective r))
          (H (indexFourCell H hinjective r)) x := by
      simpa [hcellr] using hj
    have hrSupport :
        b ∈ hpartition.indexFourSupport hinjective k hk r := by
      change b ∈ ErdosProblems.E274.indexFourSupport
        A (H (indexFourCell H hinjective r))
          ((g k)⁻¹ * g (indexFourCell H hinjective r))
          (by simpa [A] using hk)
          (hpartition.indexFourAnchorDisjoint hinjective k hk r)
      simpa [hxLabel] using mem_indexFourSupport_of_point
        A (H (indexFourCell H hinjective r))
          ((g k)⁻¹ * g (indexFourCell H hinjective r)) x
          (by simpa [A] using hk)
          (hpartition.indexFourAnchorDisjoint hinjective k hk r)
          hxCell hxbox
    let ir : Inc := ⟨r, by simpa [Inc, Row] using hrSupport⟩
    have hpointSameCell : (point ir)⁻¹ * x ∈ H (cell ir) := by
      have hp : ((rep ir)⁻¹ * point ir) ∈ H (cell ir) := pointCell ir
      have hx : ((rep ir)⁻¹ * x) ∈ H (cell ir) := by
        simpa [rep, cell, ir, hcellr, InLeftCoset, mul_assoc] using hj
      have hmem := (H (cell ir)).mul_mem ((H (cell ir)).inv_mem hp) hx
      simpa [mul_assoc] using hmem
    simp only [Set.mem_iUnion]
    refine ⟨ir, ⟨Finset.mem_univ ir, ?_⟩⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change ((fiberRep ir)⁻¹ * z : A) ∈ fiberSubgroup ir
    change ((((fiberRep ir)⁻¹ * z : A) : G)) ∈ H (cell ir)
    simpa [fiberRep, x, mul_assoc] using hpointSameCell
  have hbound := Subgroup.one_le_sum_inv_index_of_leftCoset_cover
    (s := (Finset.univ : Finset Inc)) (g := fiberRep)
    (H := fiberSubgroup) hcover
  simpa [Inc, Row, fiberSubgroup, cell, indexFourInduced,
    Subgroup.relIndex] using hbound

set_option maxHeartbeats 800000 in
-- The double-counting normalization is finite but elaboration-intensive.
/-- The sum of the three fiber capacities is exactly three whenever the
ambient coset partition has reciprocal index sum one. -/
theorem IsCosetPartition.sum_indexFourCapacities_eq_three
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (hdensity : ∑ i : Fin n, (((H i).index : ℚ)⁻¹) = 1) :
    ∑ b : Fin 3,
      ∑ i : {i : IndexFourFiberRow (sortedIndexList H hinjective) //
          b ∈ hpartition.indexFourSupport hinjective k hk i},
        (((indexFourInduced H hinjective k i.1 : ℚ)⁻¹)) = 3 := by
  classical
  let Row := IndexFourFiberRow (sortedIndexList H hinjective)
  let support : Row → Finset (Fin 3) :=
    hpartition.indexFourSupport hinjective k hk
  let induced : Row → ℕ := indexFourInduced H hinjective k
  have hiNe (i : Row) : ((i : ℕ) : ℚ) ≠ 0 := by
    have hiNat : (i : ℕ) ≠ 0 := by
      rw [← indexFourCell_index H hinjective i]
      exact hfinite (indexFourCell H hinjective i)
    exact_mod_cast hiNat
  have heNe (i : Row) : ((induced i : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast indexFourInduced_ne_zero H hfinite hinjective k i
  have hrow (i : Row) :
      ((support i).card : ℚ) * ((induced i : ℕ) : ℚ)⁻¹ =
        4 * (((i : ℕ) : ℚ)⁻¹) := by
    change ((support i).card : ℚ) / (induced i : ℚ) =
      (4 : ℚ) / ((i : ℕ) : ℚ)
    rw [div_eq_div_iff (heNe i) (hiNe i)]
    exact_mod_cast (by
      simpa [support, induced, mul_comm] using
        hpartition.indexFourIndexRelation hinjective k hk i)
  have hrowSum :
      ∑ i : Row, ((((i : ℕ) : ℚ)⁻¹)) = 3 / 4 := by
    have hequiv := Fintype.sum_equiv
      (indexFourCellEquiv H hinjective k hk)
      (fun i : Row ↦ ((((i : ℕ) : ℚ)⁻¹)))
      (fun j : {j : Fin n // j ≠ k} ↦ (((H j.1).index : ℚ)⁻¹))
      (fun i ↦ by
        change (((i : ℕ) : ℚ)⁻¹) =
          (((H (indexFourCell H hinjective i)).index : ℚ)⁻¹)
        rw [indexFourCell_index H hinjective i])
    rw [hequiv]
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun j : Fin n ↦ j = k)
      (fun j : Fin n ↦ (((H j).index : ℚ)⁻¹))
    have hnonanchor :
        ∑ j : {j : Fin n // j ≠ k}, (((H j.1).index : ℚ)⁻¹) =
          1 - ((4 : ℚ)⁻¹) := by
      have hsplit' :
          (((H k).index : ℚ)⁻¹) +
              ∑ j : {j : Fin n // j ≠ k}, (((H j.1).index : ℚ)⁻¹) =
            ∑ j : Fin n, (((H j).index : ℚ)⁻¹) := by
        simpa using hsplit
      rw [hdensity, hk] at hsplit'
      linarith
    rw [hnonanchor]
    norm_num
  have hsubtypeSum (b : Fin 3) :
      (∑ i : {i : Row // b ∈ support i}, (((induced i.1 : ℚ)⁻¹))) =
        ∑ i : Row, if b ∈ support i then ((induced i : ℚ)⁻¹) else 0 := by
    simpa [Finset.sum_filter] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset Row))
        (fun i : Row ↦ ((induced i : ℚ)⁻¹))
        (p := fun i ↦ b ∈ support i))
  change (∑ b : Fin 3,
    ∑ i : {i : Row // b ∈ support i}, (((induced i.1 : ℚ)⁻¹))) = 3
  simp_rw [hsubtypeSum]
  have hcomm :
      (∑ b : Fin 3, ∑ i : Row,
          if b ∈ support i then ((induced i : ℚ)⁻¹) else 0) =
        ∑ i : Row, ∑ b : Fin 3,
          if b ∈ support i then ((induced i : ℚ)⁻¹) else 0 := by
    simpa using
      (Finset.sum_comm
        (s := (Finset.univ : Finset (Fin 3)))
        (t := (Finset.univ : Finset Row))
        (f := fun b i ↦
          if b ∈ support i then ((induced i : ℚ)⁻¹) else 0))
  rw [hcomm]
  calc
    (∑ i : Row, ∑ b : Fin 3,
        if b ∈ support i then ((induced i : ℚ)⁻¹) else 0) =
        ∑ i : Row, ((support i).card : ℚ) * ((induced i : ℚ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [← Finset.sum_filter, nsmul_eq_mul]
    _ = ∑ i : Row, 4 * ((((i : ℕ) : ℚ)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hrow i
    _ = 4 * ∑ i : Row, ((((i : ℕ) : ℚ)⁻¹)) := by
      rw [Finset.mul_sum]
    _ = 3 := by rw [hrowSum]; norm_num

set_option maxHeartbeats 800000 in
-- Combining the three lower bounds with their exact total uses finite linear arithmetic.
/-- Ambient reciprocal density supplies the previously isolated exact
per-fiber capacity identity. -/
theorem IsCosetPartition.indexFourCapacity_of_density
    {G : Type u} [Group G] {n : ℕ}
    {g : Fin n → G} {H : Fin n → Subgroup G}
    (hpartition : IsCosetPartition g H)
    (hfinite : ∀ i, (H i).index ≠ 0)
    (hinjective : Function.Injective (fun i ↦ (H i).index))
    (k : Fin n) (hk : (H k).index = 4)
    (hdensity : ∑ i : Fin n, (((H i).index : ℚ)⁻¹) = 1) :
    hpartition.IndexFourCapacity hinjective k hk := by
  classical
  let cap : Fin 3 → ℚ := fun b ↦
    ∑ i : {i : IndexFourFiberRow (sortedIndexList H hinjective) //
        b ∈ hpartition.indexFourSupport hinjective k hk i},
      (((indexFourInduced H hinjective k i.1 : ℚ)⁻¹))
  have hsum : ∑ b : Fin 3, cap b = 3 := by
    simpa [cap] using hpartition.sum_indexFourCapacities_eq_three
      hfinite hinjective k hk hdensity
  have hsum3 : cap 0 + cap 1 + cap 2 = 3 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have h0 : 1 ≤ cap 0 := by
    simpa [cap] using hpartition.one_le_indexFourCapacity
      hfinite hinjective k hk (0 : Fin 3)
  have h1 : 1 ≤ cap 1 := by
    simpa [cap] using hpartition.one_le_indexFourCapacity
      hfinite hinjective k hk (1 : Fin 3)
  have h2 : 1 ≤ cap 2 := by
    simpa [cap] using hpartition.one_le_indexFourCapacity
      hfinite hinjective k hk (2 : Fin 3)
  intro b
  change cap b = 1
  fin_cases b
  · change cap 0 = 1
    linarith
  · change cap 1 = 1
    linarith
  · change cap 2 = 1
    linarith

end ErdosProblems.E274
