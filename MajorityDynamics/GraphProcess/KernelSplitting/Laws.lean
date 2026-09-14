import MajorityDynamics.GraphProcess.KernelSplitting.Degrees

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting
open Universal BlockDecomposition FineKernel KernelInputs KernelEdgeSplitting
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The actual next-degree point event is exactly its internal fixed-degree graph
neighborhood event, with no supplementary normalization or law premise. -/
theorem internal_degree_real (σ : FineState.State V n) (s : History (n+1))
    (v : Block σ.part s) (b : Bool) (a : ℤ) :
    (componentLaw σ).real {F | (sampleNext σ F).deg v (append s b) = a} =
      (fixedDegreeLaw (fun w : Block σ.part s => (σ.deg w s).toNat)).real
        {G | ((G.neighborFinset v ∩ childInBlock σ s b).card : ℤ) = a} := by
  simpa only [Set.mem_ofPred_eq, sampleNext_internal_degree] using
    internalSample_real σ s
      {G | ((G.neighborFinset v ∩ childInBlock σ s b).card : ℤ) = a}

/-- Both cross orientations have the actual bipartite fixed-degree point law. -/
theorem cross_degree_real (σ : FineState.State V n) (s t : History (n+1))
    (hst : s ≠ t) (v : Block σ.part s) (b : Bool) (a : ℤ) :
    (componentLaw σ).real {F | (sampleNext σ F).deg v (append t b) = a} =
      (bipartiteFixedDegreeLaw (fun w : Block σ.part s => (σ.deg w t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat)).real
        {E | ((leftNeighbors E v ∩ childInBlock σ t b).card : ℤ) = a} := by
  simpa only [Set.mem_ofPred_eq, sampleNext_cross_degree] using
    crossSample_real σ s t hst
      {E | ((leftNeighbors E v ∩ childInBlock σ t b).card : ℤ) = a}

/-- Negative integer targets have zero actual component probability. -/
theorem negative_degree_real (σ : FineState.State V n) (x : V)
    (t : History (n+1)) (b : Bool) (a : ℤ) (ha : a < 0) :
    (componentLaw σ).real {F | (sampleNext σ F).deg x (append t b) = a} = 0 := by
  have he : {F | (sampleNext σ F).deg x (append t b) = a} = (∅ : Set (ComponentFiber σ.part σ.deg)) := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hn := next_degree_nonneg σ F x t b
    omega
  rw [he, measureReal_empty]

/-- Targets above the actual parent degree have zero actual component probability. -/
theorem above_parent_degree_real (σ : FineState.State V n) (x : V)
    (t : History (n+1)) (b : Bool) (a : ℤ) (ha : σ.deg x t < a) :
    (componentLaw σ).real {F | (sampleNext σ F).deg x (append t b) = a} = 0 := by
  have he : {F | (sampleNext σ F).deg x (append t b) = a} = (∅ : Set (ComponentFiber σ.part σ.deg)) := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hn := next_degree_le_parent σ F x t b
    omega
  rw [he, measureReal_empty]

end MajorityDynamics.GraphProcess.KernelSplitting
