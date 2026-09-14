import MajorityDynamics.GraphProcess.BlockDecomposition.Basic

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.BlockPairLaws

/-- An ordered label pair is diagonal or one of the two orientations of a strict pair. -/
def pairDecomposition (L : Type*) [LinearOrder L] :
    (L × L) ≃ L ⊕ (BlockDecomposition.Pair L ⊕ BlockDecomposition.Pair L) where
  toFun p := if h : p.1 = p.2 then Sum.inl p.1 else
    if hlt : p.1 < p.2 then Sum.inr (Sum.inl ⟨p, hlt⟩)
    else Sum.inr (Sum.inr ⟨(p.2, p.1), lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)⟩)
  invFun := fun x => match x with
    | Sum.inl s => (s, s)
    | Sum.inr (Sum.inl p) => p.val
    | Sum.inr (Sum.inr p) => (p.val.2, p.val.1)
  left_inv := by
    rintro ⟨s, t⟩
    dsimp
    split_ifs with h hlt
    · simp [h]
    · rfl
    · rfl
  right_inv := by
    rintro (s | (⟨⟨s, t⟩, h⟩ | ⟨⟨s, t⟩, h⟩))
    · simp
    · simp [ne_of_lt h, h]
    · simp [ne_of_gt h, not_lt_of_gt h]

/-- Split the full ordered block-pair product into diagonal factors and unordered pairs. -/
theorem prod_block_pairs {L M : Type*} [Fintype L] [LinearOrder L] [CommMonoid M]
    (f : L → L → M) :
    (∏ s, ∏ t, f s t) = (∏ s, f s s) *
      ∏ p : BlockDecomposition.Pair L, (f p.val.1 p.val.2 * f p.val.2 p.val.1) := by
  let g : L ⊕ (BlockDecomposition.Pair L ⊕ BlockDecomposition.Pair L) → M :=
    fun x => match x with
      | Sum.inl s => f s s
      | Sum.inr (Sum.inl p) => f p.val.1 p.val.2
      | Sum.inr (Sum.inr p) => f p.val.2 p.val.1
  have he := Fintype.prod_equiv (pairDecomposition L).symm g
    (fun p : L × L => f p.1 p.2) (by
      rintro (s | (p | p)) <;> rfl)
  simpa only [Fintype.prod_sum_type, Fintype.prod_prod_type, g,
    ← Finset.prod_mul_distrib] using he.symm

end MajorityDynamics.GraphProcess.BlockPairLaws
