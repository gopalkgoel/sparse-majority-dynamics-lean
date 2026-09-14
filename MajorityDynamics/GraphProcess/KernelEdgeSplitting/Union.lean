import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Basic

/-! Finite-union assembly under the actual fine-state transition kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The deterministic partition identity has no failure cost under the actual kernel. -/
theorem K_splitEdges_failure_eq_edges (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) :
    (FineKernel.K σ).real {τ | ¬ SplitEdgesGood y p C σ τ} =
      (FineKernel.K σ).real {τ | ¬ EdgesGood y p C σ τ} := by
  simp only [measureReal_def, FineKernel.K_apply]
  congr 2
  ext F
  simp only [Set.mem_ofPred_eq, SplitEdgesGood, FineKernel.sampleNext_part, true_and]

/-- There are exactly `2^(2*n+4)` ordered pairs of children. -/
theorem child_pair_count (n : ℕ) :
    Fintype.card (History (n+1) × History (n+1) × Bool × Bool) = 2^(2*n+4) := by
  simp only [Fintype.card_prod, history_card, Fintype.card_bool]
  calc
    2^(n+1) * (2^(n+1) * (2*2)) = 2^(n+1) * 2^(n+1) * 2^2 := by ring
    _ = 2^((n+1)+(n+1)+2) := by rw [← pow_add, ← pow_add]
    _ = _ := by congr 1; omega

/-- Union bound for all the literal S3 inequalities under the actual kernel. -/
theorem K_edges_failure_le (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (N : ℕ)
    (hpair : ∀ s t b c, (FineKernel.K σ).real
      {τ | ¬ EdgeGood y p C σ τ s t b c} ≤ 2 / Real.log N) :
    (FineKernel.K σ).real {τ | ¬ EdgesGood y p C σ τ} ≤ unionError n N := by
  let I := History (n+1) × History (n+1) × Bool × Bool
  let bad : I → Set (FineState.State V (n+1)) := fun i =>
    {τ | ¬ EdgeGood y p C σ τ i.1 i.2.1 i.2.2.1 i.2.2.2}
  have he : {τ | ¬ EdgesGood y p C σ τ} = ⋃ i : I, bad i := by
    ext τ
    simp only [EdgesGood, Set.mem_ofPred_eq, not_forall, Set.mem_iUnion,
      Prod.exists, bad, I]
  rw [he]
  calc
    (FineKernel.K σ).real (⋃ i : I, bad i) ≤
        ∑ i : I, (FineKernel.K σ).real (bad i) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _i : I, (2 : ℝ) / Real.log N := by
      exact Finset.sum_le_sum fun i _ => hpair i.1 i.2.1 i.2.2.1 i.2.2.2
    _ = unionError n N := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, I,
        child_pair_count, Nat.cast_pow, Nat.cast_ofNat, unionError]
      rw [← mul_div_assoc, ← pow_succ]

/-- S1 holds surely, so the same finite-union bound proves S1 and S3 together. -/
theorem K_splitEdges_failure_le (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (N : ℕ)
    (hpair : ∀ s t b c, (FineKernel.K σ).real
      {τ | ¬ EdgeGood y p C σ τ s t b c} ≤ 2 / Real.log N) :
    (FineKernel.K σ).real {τ | ¬ SplitEdgesGood y p C σ τ} ≤ unionError n N := by
  rw [K_splitEdges_failure_eq_edges]
  exact K_edges_failure_le y p C σ N hpair

/-- Adding an independently established S2 bound yields the unchanged S1--S3
consumer used by `LocalTransition`. -/
theorem K_kernelGood_failure_le (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (er es : ℝ)
    (hregular : (FineKernel.K σ).real
      {τ | ¬ CoarseKernel.Regular p τ.part τ.deg} ≤ er)
    (hedges : (FineKernel.K σ).real {τ | ¬ SplitEdgesGood y p C σ τ} ≤ es) :
    (FineKernel.K σ).real {τ | ¬ LocalTransition.KernelGood y p C σ τ} ≤ er + es := by
  have he : {τ | ¬ LocalTransition.KernelGood y p C σ τ} =
      {τ | ¬ CoarseKernel.Regular p τ.part τ.deg} ∪
        {τ | ¬ SplitEdgesGood y p C σ τ} := by
    ext τ
    simp only [Set.mem_ofPred_eq, Set.mem_union, kernelGood_iff]
    tauto
  rw [he]
  exact (measureReal_union_le _ _).trans (add_le_add hregular hedges)

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
