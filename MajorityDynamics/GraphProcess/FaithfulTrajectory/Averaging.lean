import MajorityDynamics.GraphProcess.CoarseKernel.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory

/-- Finite current-state averaging. Only conditional laws at the current time
are used; no assertion about conditioning on earlier states occurs. -/
theorem finite_current_state_bound {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (good : Set α) (A : Set Ω) (ε : ℝ≥0∞)
    (hstep : ∀ x ∈ good, 0 < μ (X ⁻¹' {x}) →
      cond μ (X ⁻¹' {x}) A ≤ ε) :
    μ A ≤ μ (X ⁻¹' goodᶜ) + ε := by
  classical
  let B := A ∩ X ⁻¹' good
  have htotal (E : Set Ω) :
      ∑ x, μ (X ⁻¹' {x}) * cond μ (X ⁻¹' {x}) E = μ E := by
    have h := congrArg (fun ν : Measure Ω => ν E) (sum_meas_smul_cond_fiber hX μ)
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul] using h
  have hB : μ B ≤ ε := by
    rw [← htotal B]
    calc
      _ ≤ ∑ x, μ (X ⁻¹' {x}) * ε := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hz : μ (X ⁻¹' {x}) = 0
        · simp [hz]
        refine mul_le_mul le_rfl ?_ (by positivity) (by positivity)
        by_cases hx : x ∈ good
        · exact (measure_mono Set.inter_subset_left).trans
            (hstep x hx (pos_iff_ne_zero.mpr hz))
        · have he : (X ⁻¹' {x}) ∩ B = ∅ := by
            ext ω
            simp only [B, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
              Set.mem_empty_iff_false, iff_false, not_and]
            intro h _ hg
            exact hx (h ▸ hg)
          rw [cond_apply (hX (MeasurableSet.singleton x)), he, measure_empty, mul_zero]
          exact zero_le
      _ = ε := by
        rw [← Finset.sum_mul]
        have hs : ∑ x, μ (X ⁻¹' {x}) = 1 := by
          simpa using (sum_measure_preimage_singleton (μ := μ) Finset.univ
            (fun x _ => hX (MeasurableSet.singleton x)))
        rw [hs, one_mul]
  calc
    μ A ≤ μ ((X ⁻¹' goodᶜ) ∪ B) := measure_mono (by
      intro ω hω
      by_cases h : X ω ∈ good
      · exact Or.inr ⟨hω,h⟩
      · exact Or.inl h)
    _ ≤ μ (X ⁻¹' goodᶜ) + μ B := measure_union_le _ _
    _ ≤ μ (X ⁻¹' goodᶜ) + ε := add_le_add le_rfl hB

end MajorityDynamics.GraphProcess.FaithfulTrajectory
