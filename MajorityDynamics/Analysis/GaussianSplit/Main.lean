import MajorityDynamics.Analysis.GaussianSplit.Regression
import MajorityDynamics.Analysis.GaussianSplit.ProjectionIndependence
import MajorityDynamics.Analysis.GaussianSplit.ResidualMean

/-!
# The Gaussian positive-split theorem

This completes the analytic argument in Steps 2–4 of the paper's coherence
proof. The history span may be zero-dimensional. All independence statements
are proved under the original Gaussian, then transported to the conditioned
laws; those conditioned laws are never assumed Gaussian.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace MajorityDynamics.Analysis.GaussianSplit

/-- Positive conditional covariance with the last decision, and zero
conditional covariance with the history, imply a strict increase of the
response mean on the positive child. -/
theorem standard_positive_split : StandardSplitTheorem := by
  intro d V A hA
  dsimp only
  intro hE hPD a z c hzero hpos
  have ha : a ∈ Vᗮ :=
    orthogonal_of_conditional_covariance_zero V A hA hE hPD a hzero
      (indepFun_inner_starProjection V (V.sub_starProjection_mem_orthogonal a))
  let y := z - V.starProjection z
  have hy : y ∈ Vᗮ := V.sub_starProjection_mem_orthogonal z
  have hcross : 0 < ⟪a, y⟫ := by
    rw [← conditional_cross_covariance_eq_inner V A hA hE a z hzero
      (indepFun_inner_pair_starProjection V ha hy)]
    exact hpos
  obtain ⟨hy0, hα, hr, hry⟩ := regression_coefficient_facts V a y ha hy hcross
  let α := ⟪a, y⟫ / ⟪y, y⟫
  let r := a - α • y
  let U : Space d → ℝ := fun h => -c - linear (V.starProjection z) h
  have hv : (⟨⟪y, y⟫, real_inner_self_nonneg⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have hh := congrArg (fun v : ℝ≥0 => (v : ℝ)) h
    exact (ne_of_gt (real_inner_self_pos.mpr hy0)) hh
  have hresponse : (fun x => 0 + α * linear y x + linear r x) = linear a := by
    ext x
    simp only [linear, r, inner_sub_left, real_inner_smul_left]
    ring
  have hdecision (x : Space d) :
      linear z x = linear (V.starProjection z) (V.starProjection x) + linear y x := by
    have hp := congrFun (linear_projection_of_mem V (V.starProjection_apply_mem z)) x
    change linear (V.starProjection z) (V.starProjection x) =
      linear (V.starProjection z) x at hp
    rw [hp]
    dsimp [linear, y]
    rw [inner_sub_left]
    ring
  have hchild :
      {x : Space d | V.starProjection x ∈ A ∧ U (V.starProjection x) < linear y x} =
        V.starProjection ⁻¹' A ∩ {x | 0 < c + linear z x} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hx, hlt⟩
      refine ⟨hx, ?_⟩
      dsimp [U] at hlt
      linarith [hdecision x]
    · rintro ⟨hx, hlt⟩
      refine ⟨hx, ?_⟩
      dsimp [U]
      linarith [hdecision x]
  have h := residual_mean_increase (stdGaussian (Space d)) V.starProjection
    (linear r) (linear y) V.starProjection.measurable (measurable_linear r)
    (measurable_linear y) (memLp_linear r IsGaussian.memLp_two_id)
    (memLp_linear y IsGaussian.memLp_two_id) (integral_linear_standard r)
    (indepFun_inner_prod_starProjection V hr hry)
    (indepFun_inner_starProjection V hy).symm
    (⟨⟪y, y⟫, real_inner_self_nonneg⟩ : ℝ≥0) hv (linear_standard_gaussian_law y)
    (U := U) hA hE (by fun_prop) 0 α hα
  rw [hresponse, hchild] at h
  exact h

end MajorityDynamics.Analysis.GaussianSplit
