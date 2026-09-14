import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Laws

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting
open Universal BlockDecomposition FineKernel KernelInputs KernelEdgeSplitting
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- An actual next degree is the component graph's literal neighbor count in the
fixed target child, in either ordered orientation (including the diagonal). -/
theorem sampleNext_cross_degree (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (s t : History (n+1))
    (v : Block σ.part s) (b : Bool) :
    (sampleNext σ F).deg v (append t b) =
      ((leftNeighbors (crossSample σ s t F) v ∩ childInBlock σ t b).card : ℤ) := by
  change History.degreeArray (FineState.refinement σ) (componentGraph σ F)
    v.val (append t b) = _
  unfold History.degreeArray
  rw [← RowArray.childSet_stateArray σ t b]
  change (∑ w ∈ child σ t b, if (componentGraph σ F).Adj v.val w then (1 : ℤ) else 0) = _
  rw [← childInBlock_map σ t b, Finset.sum_map]
  have he : leftNeighbors (crossSample σ s t F) v ∩ childInBlock σ t b =
      (childInBlock σ t b).filter (fun w => (componentGraph σ F).Adj v.val w.val) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_filter]
    have hw : w ∈ leftNeighbors (crossSample σ s t F) v ↔
        (componentGraph σ F).Adj v.val w.val := by
      exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ w))
    rw [hw]
    exact and_comm
  rw [he]
  exact Finset.sum_boole _ _

/-- The diagonal case uses the actual loopless internal graph; self exclusion is
therefore supplied by its neighbor finset, not a separate convention. -/
theorem sampleNext_internal_degree (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (s : History (n+1))
    (v : Block σ.part s) (b : Bool) :
    (sampleNext σ F).deg v (append s b) =
      (((internalSample σ s F).neighborFinset v ∩ childInBlock σ s b).card : ℤ) := by
  rw [sampleNext_cross_degree σ F s s v b]
  apply congrArg (fun U : Finset (Block σ.part s) =>
    ((U ∩ childInBlock σ s b).card : ℤ))
  ext w
  simp only [leftNeighbors, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]
  exact glue_internal σ.part (fiberComponents σ.part σ.deg F) s v w

/-- Sampled degrees have their literal nonnegative integer support. -/
theorem next_degree_nonneg (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (x : V) (t : History (n+1)) (b : Bool) :
    0 ≤ (sampleNext σ F).deg x (append t b) :=
  state_degree_nonneg (sampleNext σ F) x (append t b)

/-- Restricting neighbors to one child cannot exceed the original parent degree. -/
theorem next_degree_le_parent (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (x : V) (t : History (n+1)) (b : Bool) :
    (sampleNext σ F).deg x (append t b) ≤ σ.deg x t := by
  have hG : History.degreeArray σ.part (componentGraph σ F) = σ.deg :=
    (fiberGlue σ.part σ.deg F).property
  rw [← hG]
  change History.degreeArray (FineState.refinement σ) (componentGraph σ F)
    x (append t b) ≤ _
  rw [History.degreeArray_eq_card, History.degreeArray_eq_card,
    ← RowArray.childSet_stateArray σ t b]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (child_subset σ t b))

/-- Every actual next degree belongs to the finite target range zero through |V|. -/
theorem next_degree_le_card (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (x : V) (t : History (n+1)) (b : Bool) :
    (sampleNext σ F).deg x (append t b) ≤ (Fintype.card V : ℤ) := by
  change History.degreeArray (FineState.refinement σ) (componentGraph σ F)
    x (append t b) ≤ _
  rw [History.degreeArray_eq_card]
  exact_mod_cast Finset.card_le_univ _

end MajorityDynamics.GraphProcess.KernelSplitting
