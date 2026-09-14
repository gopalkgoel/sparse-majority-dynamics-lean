import MajorityDynamics.Probability.FixedDegreeSampling.BipartiteBasic
noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {L R : Type*} [Fintype L] [Fintype R]

def deleteLeft (v : L) (E : CrossEdges L R) : CrossEdges (Remaining v) R :=
  {x | (x.1.val, x.2) ∈ E}
def insertLeft (v : L) (S : Finset R) (E : CrossEdges (Remaining v) R) : CrossEdges L R :=
  {x | if h : x.1 = v then x.2 ∈ S else (⟨x.1, h⟩, x.2) ∈ E}

omit [Fintype L] [Fintype R] in
@[simp] theorem deleteLeft_insertLeft (v : L) (S : Finset R)
    (E : CrossEdges (Remaining v) R) : deleteLeft v (insertLeft v S E) = E := by
  ext x
  simp [deleteLeft, insertLeft, x.1.property]

omit [Fintype L] in
theorem insertLeft_deleteLeft (v : L) (S : Finset R) (E : CrossEdges L R)
    (h : leftNeighbors E v = S) : insertLeft v S (deleteLeft v E) = E := by
  ext ⟨u, w⟩
  change _ ↔ (u, w) ∈ E
  by_cases hx : u = v
  · subst u
    simp [insertLeft, ← h, leftNeighbors]
  · simp [insertLeft, deleteLeft, hx]

omit [Fintype L] in
theorem insertLeft_neighborhood (v : L) (S : Finset R)
    (E : CrossEdges (Remaining v) R) : leftNeighbors (insertLeft v S E) v = S := by
  ext w
  simp [leftNeighbors, insertLeft]

omit [Fintype L] in
theorem deleteLeft_leftDegree (v : L) (E : CrossEdges L R) (u : Remaining v) :
    leftDegree (deleteLeft v E) u = leftDegree E u := rfl

omit [Fintype R] in
theorem deleteLeft_rightDegree (v : L) (E : CrossEdges L R) (w : R) :
    rightDegree (deleteLeft v E) w = rightDegree E w - if (v, w) ∈ E then 1 else 0 := by
  have hm : (rightNeighbors (deleteLeft v E) w).map (Function.Embedding.subtype _) =
      (rightNeighbors E w).erase v := by
    ext u
    simp only [Finset.mem_map, rightNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    change (∃ a : Remaining v, (a.val, w) ∈ E ∧ a.val = u) ↔ u ≠ v ∧ (u, w) ∈ E
    aesop
  have hc := congrArg Finset.card hm
  simp only [Finset.card_map] at hc
  rw [rightDegree, hc]
  by_cases h : (v, w) ∈ E
  · rw [if_pos h, Finset.card_erase_of_mem (by simpa [rightNeighbors] using h)]
    rfl
  · rw [if_neg h, Finset.erase_eq_of_notMem (by simpa [rightNeighbors] using h), Nat.sub_zero]
    rfl

omit [Fintype R] in
theorem insertLeft_rightDegree (v : L) (S : Finset R)
    (E : CrossEdges (Remaining v) R) (w : R) :
    rightDegree (insertLeft v S E) w = rightDegree E w + if w ∈ S then 1 else 0 := by
  have hd := deleteLeft_rightDegree v (insertLeft v S E) w
  rw [deleteLeft_insertLeft] at hd
  by_cases hw : w ∈ S
  · have hp : 0 < rightDegree (insertLeft v S E) w := by
      apply Finset.card_pos.mpr
      exact ⟨v, by simp [rightNeighbors, insertLeft, hw]⟩
    have he : (v, w) ∈ insertLeft v S E := by simp [insertLeft, hw]
    rw [if_pos he] at hd
    simp only [hw, ite_true]
    omega
  · simpa [insertLeft, hw] using hd.symm

theorem bipartite_neighborhood_admissible (a : L → ℕ) (b : R → ℕ) (v : L)
    (S : Finset R) (E : bipartiteNeighborhoodFiber a b v S) :
    bipartiteAdmissible a b v S := by
  refine ⟨?_, ?_⟩
  · rw [← E.property.2]; exact E.property.1.1 v
  · intro w hw
    have hp : 0 < rightDegree E.val w := by
      apply Finset.card_pos.mpr
      refine ⟨v, ?_⟩
      simpa [rightNeighbors, ← E.property.2, leftNeighbors] using hw
    rw [E.property.1.2 w] at hp
    exact hp

/-- Explicit deletion/insertion equivalence; no residual nonemptiness is required. -/
def bipartite_neighborhood_removal_equiv (a : L → ℕ) (b : R → ℕ) (v : L)
    (S : Finset R) (h : bipartiteAdmissible a b v S) :
    bipartiteNeighborhoodFiber a b v S ≃
      bipartiteFamily (fun u : Remaining v => a u) (residualRightDegree b S) where
  toFun E := ⟨deleteLeft v E.val, by
    constructor
    · intro u; exact E.property.1.1 u
    · intro w
      rw [deleteLeft_rightDegree, E.property.1.2]
      simp [residualRightDegree, ← E.property.2, leftNeighbors]⟩
  invFun E := ⟨insertLeft v S E.val, by
    refine ⟨⟨?_, ?_⟩, insertLeft_neighborhood v S E.val⟩
    · intro u
      by_cases hu : u = v
      · subst u
        rw [leftDegree, insertLeft_neighborhood]; exact h.1
      · have he : leftDegree (insertLeft v S E.val) u = leftDegree E.val ⟨u, hu⟩ := by
          simp [leftDegree, leftNeighbors, insertLeft, hu]
        rw [he]; exact E.property.1 ⟨u, hu⟩
    · intro w
      rw [insertLeft_rightDegree, E.property.2, residualRightDegree]
      apply Nat.sub_add_cancel
      split_ifs with hw
      · exact h.2 w hw
      · exact Nat.zero_le _⟩
  left_inv E := Subtype.ext (insertLeft_deleteLeft v S E.val E.property.2)
  right_inv E := Subtype.ext (deleteLeft_insertLeft v S E.val)
end MajorityDynamics.Probability.FixedDegreeSampling
