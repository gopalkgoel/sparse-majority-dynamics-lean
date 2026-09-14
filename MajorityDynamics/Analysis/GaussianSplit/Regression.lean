import MajorityDynamics.Analysis.GaussianSplit.Basic
import MajorityDynamics.Analysis.GaussianSplit.Conditioning

/-!
# Regression before and after a history restriction

The covariance of the conditioned law is used only for linear algebra. Gaussian
independence is established under the original law and transported by the
conditioning lemmas.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace MajorityDynamics.Analysis.GaussianSplit

variable {d : ℕ}

@[fun_prop] theorem measurable_linear (a : Space d) : Measurable (linear a) :=
  (innerSL ℝ a).measurable

theorem memLp_linear (a : Space d) {ρ : Measure (Space d)}
    (hρ : MemLp id 2 ρ) : MemLp (linear a) 2 ρ :=
  (innerSL ℝ a).comp_memLp' hρ

theorem integral_linear_standard (a : Space d) :
    ∫ x, linear a x ∂stdGaussian (Space d) = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ a)

theorem covariance_linear {ρ : Measure (Space d)} [IsFiniteMeasure ρ]
    (hρ : MemLp id 2 ρ) (a b : Space d) :
    covariance (linear a) (linear b) ρ = covarianceBilin ρ a b :=
  (covarianceBilin_apply_eq_cov hρ a b).symm

theorem covariance_linear_standard (a b : Space d) :
    covariance (linear a) (linear b) (stdGaussian (Space d)) = ⟪a, b⟫ := by
  rw [covariance_linear IsGaussian.memLp_two_id, covarianceBilin_stdGaussian]
  rfl

theorem linear_projection_of_mem (V : Submodule ℝ (Space d)) {a : Space d}
    (ha : a ∈ V) : linear a ∘ V.starProjection = linear a := by
  ext x
  change ⟪a, V.starProjection x⟫ = ⟪a, x⟫
  rw [← V.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr ha]

theorem linear_projection_orthogonal_of_mem (V : Submodule ℝ (Space d))
    {a : Space d} (ha : a ∈ Vᗮ) :
    linear a ∘ Vᗮ.starProjection = linear a :=
  linear_projection_of_mem Vᗮ ha

/-- A residual independent of the history remains uncorrelated with every
linear combination of history coordinates. -/
theorem conditional_covariance_of_orthogonal
    (V : Submodule ℝ (Space d)) (A : Set (Space d)) (hA : MeasurableSet A)
    (hE : (stdGaussian (Space d)) (V.starProjection ⁻¹' A) ≠ 0)
    (a p : Space d) (hp : p ∈ V)
    (hind : IndepFun (linear a) V.starProjection (stdGaussian (Space d))) :
    covarianceBilin (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) a p = 0 := by
  let ρ := stdGaussian (Space d)
  let E := V.starProjection ⁻¹' A
  have : IsProbabilityMeasure (cond ρ E) := cond_isProbabilityMeasure hE
  rw [covarianceBilin_apply_eq_cov (memLp_cond IsGaussian.memLp_two_id hE)]
  change covariance (linear a) (linear p) (cond ρ E) = 0
  rw [← linear_projection_of_mem V hp]
  apply covariance_cond_preimage_eq_zero_of_indepFun hind V.starProjection.measurable hA hE
    (measurable_linear p) (memLp_linear a IsGaussian.memLp_two_id)
  rw [linear_projection_of_mem V hp]
  exact memLp_linear p IsGaussian.memLp_two_id

/-- Vanishing conditioned covariances force the original Gaussian projection
of the response onto the history span to be zero. -/
theorem orthogonal_of_conditional_covariance_zero
    (V : Submodule ℝ (Space d)) (A : Set (Space d)) (hA : MeasurableSet A)
    (hE : (stdGaussian (Space d)) (V.starProjection ⁻¹' A) ≠ 0)
    (hPD : ∀ v : Space d, v ≠ 0 →
      0 < covarianceBilin (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) v v)
    (a : Space d)
    (hzero : ∀ v ∈ V,
      covarianceBilin (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) a v = 0)
    (hind : IndepFun (linear (a - V.starProjection a)) V.starProjection
      (stdGaussian (Space d))) : a ∈ Vᗮ := by
  let p := V.starProjection a
  have hp : p ∈ V := V.starProjection_apply_mem a
  have hr := conditional_covariance_of_orthogonal V A hA hE (a - p) p hp hind
  have hzero' := hzero p hp
  have hpp : covarianceBilin
      (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) p p = 0 := by
    simpa only [map_sub, sub_apply, hzero', zero_sub, neg_eq_zero]
      using hr
  have hp0 : p = 0 := by
    by_contra hn
    exact (ne_of_gt (hPD p hn)) hpp
  have hmem := V.sub_starProjection_mem_orthogonal a
  simpa only [show V.starProjection a = 0 from hp0, sub_zero] using hmem

/-- Conditioning does not alter a covariance of two residuals jointly
independent of the history. -/
theorem conditional_covariance_eq_inner_of_residuals
    (V : Submodule ℝ (Space d)) (A : Set (Space d)) (hA : MeasurableSet A)
    (hE : (stdGaussian (Space d)) (V.starProjection ⁻¹' A) ≠ 0)
    (a b : Space d)
    (hind : IndepFun (fun x => (linear a x, linear b x)) V.starProjection
      (stdGaussian (Space d))) :
    covarianceBilin (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) a b =
      ⟪a, b⟫ := by
  have : IsProbabilityMeasure
      (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) :=
    cond_isProbabilityMeasure hE
  rw [covarianceBilin_apply_eq_cov (memLp_cond IsGaussian.memLp_two_id hE)]
  change covariance (linear a) (linear b)
    (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) = _
  rw [covariance_cond_preimage_of_indepFun hind (measurable_linear a)
    (measurable_linear b) V.starProjection.measurable hA hE,
    covariance_linear_standard]

/-- Once the response is orthogonal to the histories, its covariance with the
last decision is its ordinary Gaussian covariance with the decision residual. -/
theorem conditional_cross_covariance_eq_inner
    (V : Submodule ℝ (Space d)) (A : Set (Space d)) (hA : MeasurableSet A)
    (hE : (stdGaussian (Space d)) (V.starProjection ⁻¹' A) ≠ 0)
    (a z : Space d)
    (hzero : ∀ v ∈ V,
      covarianceBilin (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) a v = 0)
    (hind : IndepFun (fun x => (linear a x, linear (z - V.starProjection z) x))
      V.starProjection (stdGaussian (Space d))) :
    covarianceBilin (cond (stdGaussian (Space d)) (V.starProjection ⁻¹' A)) a z =
      ⟪a, z - V.starProjection z⟫ := by
  have h := conditional_covariance_eq_inner_of_residuals V A hA hE
    a (z - V.starProjection z) hind
  simpa only [map_sub, hzero _ (V.starProjection_apply_mem z), sub_zero] using h

/-- The one-dimensional regression slope is strictly positive, and its
remaining coefficient is orthogonal both to the last residual and history. -/
theorem regression_coefficient_facts
    (V : Submodule ℝ (Space d)) (a y : Space d) (ha : a ∈ Vᗮ) (hy : y ∈ Vᗮ)
    (hcross : 0 < ⟪a, y⟫) :
    y ≠ 0 ∧
    0 < ⟪a, y⟫ / ⟪y, y⟫ ∧
    a - (⟪a, y⟫ / ⟪y, y⟫) • y ∈ Vᗮ ∧
    ⟪a - (⟪a, y⟫ / ⟪y, y⟫) • y, y⟫ = 0 := by
  have hy0 : y ≠ 0 := by
    intro h
    simp [h] at hcross
  have hyy : 0 < ⟪y, y⟫ := real_inner_self_pos.mpr hy0
  refine ⟨hy0, div_pos hcross hyy, Vᗮ.sub_mem ha (Vᗮ.smul_mem _ hy), ?_⟩
  rw [inner_sub_left, real_inner_smul_left, div_mul_cancel₀ _ (ne_of_gt hyy), sub_self]

/-- The nonzero last residual is a centered Gaussian with positive variance. -/
theorem linear_standard_gaussian_law (y : Space d) :
    (stdGaussian (Space d)).map (linear y) =
      gaussianReal 0 (⟨⟪y, y⟫, real_inner_self_nonneg⟩ : ℝ≥0) := by
  have hg : HasGaussianLaw (linear y) (stdGaussian (Space d)) :=
    HasGaussianLaw.map_of_measurable (innerSL ℝ y) IsGaussian.hasGaussianLaw_id
      (innerSL ℝ y).measurable
  rw [hg.map_eq_gaussianReal, integral_linear_standard]
  congr 1
  rw [← covariance_self (measurable_linear y).aemeasurable, covariance_linear_standard]
  ext
  simp only [Real.coe_toNNReal _ real_inner_self_nonneg]
  rfl

end MajorityDynamics.Analysis.GaussianSplit
