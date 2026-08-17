import ErdosProblems.E274.CosetPartitionBasics

/-!
# Elementary group lemmas for the E274 fiber obstruction

These lemmas formalize the local reason that two disjoint fragments in the
same anchor fiber cannot have coprime induced subgroup indices.  No theorem
from Margolis--Schnabel is used here.
-/

namespace ErdosProblems.E274

universe u

/-- If `A` has finite index and the ambient indices of `A` and `B` are
coprime, then the relative index of `A ∩ B` in `B` is the full index of `A`.
-/
theorem relIndex_eq_index_of_coprime
    {G : Type u} [Group G] (A B : Subgroup G)
    (hA : A.index ≠ 0) (hcop : Nat.Coprime A.index B.index) :
    A.relIndex B = A.index := by
  have hdvdInter : A.index ∣ (A ⊓ B).index :=
    Subgroup.index_dvd_of_le inf_le_left
  have hinter : A.relIndex B * B.index = (A ⊓ B).index := by
    simpa [Subgroup.inf_relIndex_right] using
      (Subgroup.relIndex_mul_index (H := A ⊓ B) (K := B) inf_le_right)
  have hdvd : A.index ∣ A.relIndex B := by
    apply hcop.dvd_of_dvd_mul_right
    rw [hinter]
    exact hdvdInter
  have hdne : A.relIndex B ≠ 0 := by
    intro hd
    exact hA (A.index_eq_zero_of_relIndex_eq_zero hd)
  have hle : A.relIndex B ≤ A.index := by
    have hbound := Subgroup.relIndex_le_of_le_right (H := A) (K := B)
      (L := (⊤ : Subgroup G)) le_top (by simpa using hA)
    simpa using hbound
  exact le_antisymm hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hdne) hdvd)

/-- The quotient classes of `K/(H ∩ K)` inject into the left `H`-cosets met
by the shifted cell `gK`. -/
def shiftedCellBoxEmbedding {G : Type u} [Group G]
    (H K : Subgroup G) (g : G) :
    K ⧸ H.subgroupOf K ↪ G ⧸ H where
  toFun := Quotient.map' (fun k : K ↦ g * (k : G)) (by
    intro a b hab
    simpa only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hab)
  inj' := Quotient.ind₂' (by
    intro a b hab
    change QuotientGroup.mk (g * (a : G)) =
      QuotientGroup.mk (g * (b : G)) at hab
    change QuotientGroup.mk a = QuotientGroup.mk b
    rw [QuotientGroup.eq] at hab ⊢
    simpa only [Subgroup.mem_subgroupOf, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left] using hab)

@[simp] theorem shiftedCellBoxEmbedding_apply_mk
    {G : Type u} [Group G] (H K : Subgroup G) (g : G) (k : K) :
    shiftedCellBoxEmbedding H K g (QuotientGroup.mk k) =
      QuotientGroup.mk (g * (k : G)) := rfl

/-- Coprime ambient indices force the embedding of met `H`-cosets to be
surjective. -/
theorem shiftedCellBoxEmbedding_surjective_of_coprime
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (hH : H.index ≠ 0) (hcop : Nat.Coprime H.index K.index) :
    Function.Surjective (shiftedCellBoxEmbedding H K g) := by
  letI : Fintype (G ⧸ H) := H.fintypeOfIndexNeZero hH
  have hdne : H.relIndex K ≠ 0 := by
    intro hd
    exact hH (H.index_eq_zero_of_relIndex_eq_zero hd)
  letI : Fintype (K ⧸ H.subgroupOf K) :=
    (H.subgroupOf K).fintypeOfIndexNeZero hdne
  have hcardDom :
      Fintype.card (K ⧸ H.subgroupOf K) = H.relIndex K := by
    rw [← Nat.card_eq_fintype_card, ← (H.subgroupOf K).index_eq_card]
    rfl
  have hcardCod : Fintype.card (G ⧸ H) = H.index := by
    rw [← Nat.card_eq_fintype_card, ← H.index_eq_card]
  have hcard :
      Fintype.card (K ⧸ H.subgroupOf K) = Fintype.card (G ⧸ H) := by
    rw [hcardDom, hcardCod, relIndex_eq_index_of_coprime H K hH hcop]
  exact ((Fintype.bijective_iff_injective_and_card
    (shiftedCellBoxEmbedding H K g)).2
      ⟨(shiftedCellBoxEmbedding H K g).injective, hcard⟩).2

/-- Left cosets of finite-index subgroups with coprime indices must meet. -/
theorem leftCosets_intersect_of_coprime_indices
    {G : Type u} [Group G] (H K : Subgroup G) (a g : G)
    (hH : H.index ≠ 0) (hcop : Nat.Coprime H.index K.index) :
    ∃ x, InLeftCoset a H x ∧ InLeftCoset g K x := by
  have hsurj :=
    shiftedCellBoxEmbedding_surjective_of_coprime H K g hH hcop
  rcases hsurj (QuotientGroup.mk a) with ⟨q, hq⟩
  induction q using QuotientGroup.induction_on with
  | _ k =>
      refine ⟨g * (k : G), ?_, by simp [InLeftCoset]⟩
      rw [shiftedCellBoxEmbedding_apply_mk] at hq
      rw [InLeftCoset, ← QuotientGroup.eq]
      exact hq.symm

/-- Pairwise disjoint left cosets have subgroup-index gcd greater than one. -/
theorem gcd_gt_one_of_disjoint_leftCosets
    {G : Type u} [Group G] (H K : Subgroup G) (a g : G)
    (hH : H.index ≠ 0)
    (hdisjoint : ∀ x, ¬(InLeftCoset a H x ∧ InLeftCoset g K x)) :
    1 < Nat.gcd H.index K.index := by
  have hgcdPos : 0 < Nat.gcd H.index K.index :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hH)
  by_contra hnot
  have hgcdOne : Nat.gcd H.index K.index = 1 := by omega
  have hcop : Nat.Coprime H.index K.index := hgcdOne
  rcases leftCosets_intersect_of_coprime_indices H K a g hH hcop with
    ⟨x, hx⟩
  exact hdisjoint x hx

end ErdosProblems.E274
