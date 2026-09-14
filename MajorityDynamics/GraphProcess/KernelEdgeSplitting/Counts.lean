import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal BlockDecomposition KernelInputs
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

private theorem rectangleCount_sum {L R : Type*} [Fintype L] [Fintype R]
    (U : Finset L) (W : Finset R) (E : CrossEdges L R) :
    (rectangleCount U W E : ℤ) =
      ∑ v ∈ U, ∑ w ∈ W, if (v,w) ∈ E then (1 : ℤ) else 0 := by
  simp only [rectangleCount, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter, Finset.sum_product, Nat.cast_ite, Nat.cast_zero]

/-- Literal ordered next totals are the actual component rectangle counts, in either orientation. -/
theorem sampleNext_rectangle_count (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (p : ℝ)
    (s t : Universal.History (n+1)) (b c : Bool) :
    (CoarseKernel.rho p (FineKernel.sampleNext σ F)).realEdges
      (append s b) (append t c) =
      (rectangleCount (childInBlock σ s b) (childInBlock σ t c)
        (crossSample σ s t F) : ℝ) := by
  have h : History.edgeTotals (FineState.refinement σ)
      (History.degreeArray (FineState.refinement σ) (componentGraph σ F))
      (append s b) (append t c) =
      (rectangleCount (childInBlock σ s b) (childInBlock σ t c)
        (crossSample σ s t F) : ℤ) := by
    rw [rectangleCount_sum]
    unfold History.edgeTotals History.degreeArray
    rw [← RowArray.childSet_stateArray σ s b, ← RowArray.childSet_stateArray σ t c]
    change (∑ v ∈ child σ s b, ∑ w ∈ child σ t c,
      if (componentGraph σ F).Adj v w then (1 : ℤ) else 0) = _
    rw [← childInBlock_map σ s b, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro v _
    rw [← childInBlock_map σ t c, Finset.sum_map]
    rfl
  change (History.edgeTotals (FineState.refinement σ)
    (History.degreeArray (FineState.refinement σ) (componentGraph σ F))
    (append s b) (append t c) : ℝ) = _
  exact_mod_cast h

omit [Fintype V] in
private theorem twice_internalCount_sum (U : Finset V) (G : SimpleGraph V) :
    2 * (internalCount U G : ℤ) =
      ∑ v ∈ U, ∑ w ∈ U, if G.Adj v w then (1 : ℤ) else 0 := by
  have h := congrArg (Nat.cast : ℕ → ℤ)
    (G.induce (U : Set V)).sum_degrees_eq_twice_card_edges
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at h
  change 2 * ((G.induce (U : Set V)).edgeFinset.card : ℤ) = _
  rw [← h]
  calc
    (∑ v : (U : Set V), ((G.induce (U : Set V)).degree v : ℤ)) =
        ∑ v : (U : Set V), ∑ w : (U : Set V), if G.Adj v.val w.val then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact History.graph_degree_eq_sum (G.induce (U : Set V)) v
    _ =
        ∑ v ∈ U, ∑ w : (U : Set V), if G.Adj v w.val then (1 : ℤ) else 0 :=
      (Finset.sum_subtype U (fun _ => Iff.rfl)
        (fun v : V => ∑ w : (U : Set V), if G.Adj v w.val then (1 : ℤ) else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      exact (Finset.sum_subtype U (fun _ => Iff.rfl)
        (fun w : V => if G.Adj v w then (1 : ℤ) else 0)).symm

private theorem rectangle_internal (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (s : Universal.History (n+1))
    (U W : Finset (Block σ.part s)) :
    rectangleCount U W (crossSample σ s s F) =
      rectangleCount U W {e | (internalSample σ s F).Adj e.1 e.2} := by
  unfold rectangleCount
  congr 1
  ext e
  simp only [Finset.mem_filter, Set.mem_ofPred_eq]
  have h := glue_internal σ.part (fiberComponents σ.part σ.deg F) s e.1 e.2
  change (_ ∧ (componentGraph σ F).Adj e.1.val e.2.val) ↔ _
  exact and_congr_right fun _ => h

/-- A diagonal ordered child total counts every actual internal edge twice. -/
theorem sampleNext_internal_count (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (p : ℝ)
    (s : Universal.History (n+1)) (b : Bool) :
    (CoarseKernel.rho p (FineKernel.sampleNext σ F)).realEdges
      (append s b) (append s b) =
      2 * (internalCount (childInBlock σ s b) (internalSample σ s F) : ℝ) := by
  rw [sampleNext_rectangle_count, rectangle_internal]
  have h := (rectangleCount_sum (childInBlock σ s b) (childInBlock σ s b)
    {e | (internalSample σ s F).Adj e.1 e.2}).trans
      (twice_internalCount_sum (childInBlock σ s b) (internalSample σ s F)).symm
  exact_mod_cast h

/-- The two different children partition their actual parent, so their total is its literal cut. -/
theorem sampleNext_cut_count (σ : FineState.State V n)
    (F : ComponentFiber σ.part σ.deg) (p : ℝ)
    (s : Universal.History (n+1)) (b c : Bool) (hbc : b ≠ c) :
    (CoarseKernel.rho p (FineKernel.sampleNext σ F)).realEdges
      (append s b) (append s c) =
      (cutCount (childInBlock σ s b) (internalSample σ s F) : ℝ) := by
  have hc : c = !b := by cases b <;> cases c <;> simp_all
  rw [sampleNext_rectangle_count, rectangle_internal, hc, ← childInBlock_complement]
  congr 1
  unfold rectangleCount cutCount cutCandidates
  congr 1
  ext e
  simp only [Finset.mem_filter, Set.mem_ofPred_eq, Finset.mem_product,
    Finset.mem_sdiff, Finset.mem_univ, mem_childInBlock]

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
