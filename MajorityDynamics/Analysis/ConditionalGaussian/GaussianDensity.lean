import MajorityDynamics.Analysis.ConditionalGaussian.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The density of the concrete multivariate Gaussian

The proof starts from Mathlib's independent scalar Gaussians and transports the
density along the invertible covariance square root. No alternative Gaussian
law is introduced.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace Topology MatrixOrder

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

instance isGaussian_gaussianLaw (S : Covariance d) (γ : Space d) :
    IsGaussian (gaussianLaw S γ) := by
  unfold gaussianLaw
  infer_instance

theorem gaussianLaw_memLp (S : Covariance d) (γ : Space d)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (gaussianLaw S γ) :=
  IsGaussian.memLp_id _ p hp

theorem gaussianLaw_memLp_two (S : Covariance d) (γ : Space d) :
    MemLp id 2 (gaussianLaw S γ) :=
  gaussianLaw_memLp S γ 2 (by norm_num)

theorem gaussianLaw_integrable (S : Covariance d) (γ : Space d) :
    Integrable id (gaussianLaw S γ) :=
  IsGaussian.integrable_id

theorem gaussianLaw_integrable_norm_pow (S : Covariance d) (γ : Space d) (n : ℕ) :
    Integrable (fun x => ‖x‖ ^ n) (gaussianLaw S γ) :=
  (gaussianLaw_memLp S γ n (by simp)).integrable_norm_pow'

theorem gaussianLaw_mass_lt_top (S : Covariance d) (γ : Space d) (O : Set (Space d)) :
    gaussianLaw S γ O < ∞ :=
  measure_lt_top _ _

private theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    setLIntegral_map (f := fun y => f (e.symm y)) hs
      (hf.comp e.symm.measurable) e.measurable]
  simp

private theorem pi_stdGaussian_density :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) =
      volume.withDensity (fun x : Fin d → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x in Set.univ.pi s,
    ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))
    ∂(Measure.pi fun _ : Fin d => volume)) = _
  rw [Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_fintype_prod_eq_prod]
    simp_rw [gaussianReal_apply_eq_integral 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
    exact ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg fun x =>
      gaussianPDFReal_nonneg 0 1 x
  · exact Integrable.fintype_prod fun _ => (integrable_gaussianPDFReal 0 1).restrict
  · exact ae_of_all _ fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

private theorem stdGaussian_density :
    stdGaussian (Space d) = volume.withDensity (fun x : Space d =>
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2))) := by
  rw [← map_pi_eq_stdGaussian, pi_stdGaussian_density,
    show (WithLp.toLp 2 : (Fin d → ℝ) → Space d) = MeasurableEquiv.toLp 2 (Fin d → ℝ)
      from rfl,
    map_withDensity_equiv]
  · rw [show Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) volume = volume from
      (PiLp.volume_preserving_toLp (Fin d)).map_eq]
    congr 1
    funext x
    congr 1
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_sum]
    congr 2
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [← Finset.sum_div, ← Finset.sum_neg_distrib]
    rfl
  · fun_prop

private theorem matrixCLE_symm_apply (A : Covariance d) (hA : IsUnit A) (x : Space d) :
    (matrixCLE A hA).symm x = matrixCLM A⁻¹ x := by
  apply (matrixCLE A hA).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change x = matrixCLM A (matrixCLM A⁻¹ x)
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA), map_one]
  rfl

private theorem sqrt_inverse_norm_sq (S : Covariance d) (hS : S.PosDef)
    (hA : IsUnit (CFC.sqrt S)) (x : Space d) :
    ‖(matrixCLE (CFC.sqrt S) hA).symm x‖ ^ 2 = ⟪x, matrixCLM S⁻¹ x⟫ := by
  rw [matrixCLE_symm_apply, ← real_inner_self_eq_norm_sq]
  have hsym : IsSelfAdjoint (matrixCLM (CFC.sqrt S)⁻¹) :=
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).inv.nonneg).isSelfAdjoint.map _
  rw [← ContinuousLinearMap.adjoint_inner_right, hsym.adjoint_eq]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    ← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]

/-- The full nondegenerate multivariate Gaussian density, with one positive
normalizing constant for every mean. -/
theorem gaussianDensityFormula (S : Covariance d) (hS : S.PosDef) :
    GaussianDensityFormula S := by
  have hA : IsUnit (CFC.sqrt S) :=
    (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit
  let e := matrixCLE (CFC.sqrt S) hA
  let k : ℝ := |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹|
  have hk : 0 < k := abs_pos.mpr (inv_ne_zero e.toLinearEquiv.isUnit_det'.ne_zero)
  let c₀ : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ d
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨k * c₀, mul_pos hk hc₀, ?_⟩
  intro γ
  have hlinear : Measure.map e volume = ENNReal.ofReal k • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume e.toLinearEquiv.isUnit_det'.ne_zero
  rw [gaussianLaw, multivariateGaussian, stdGaussian_density]
  change Measure.map (fun x => γ + e x)
    (volume.withDensity (fun x : Space d =>
      ENNReal.ofReal (c₀ * Real.exp (-‖x‖ ^ 2 / 2)))) = _
  rw [show (fun x => γ + e x) =
      (MeasurableEquiv.addLeft γ) ∘ e.toHomeomorph.toMeasurableEquiv from rfl,
    ← Measure.map_map (MeasurableEquiv.addLeft γ).measurable
      e.toHomeomorph.toMeasurableEquiv.measurable,
    map_withDensity_equiv e.toHomeomorph.toMeasurableEquiv _ _ (by fun_prop)]
  rw [show Measure.map e.toHomeomorph.toMeasurableEquiv volume = ENNReal.ofReal k • volume
      from hlinear,
    withDensity_smul_measure, Measure.map_smul,
    map_withDensity_equiv (MeasurableEquiv.addLeft γ) _ _ (by fun_prop)]
  rw [show Measure.map (MeasurableEquiv.addLeft γ) volume = volume from
      map_add_left_eq_self volume γ,
    ← withDensity_smul' (ENNReal.ofReal k) _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  change ENNReal.ofReal k *
    ENNReal.ofReal (c₀ * Real.exp (-‖e.symm (-γ + x)‖ ^ 2 / 2)) = _
  rw [← ENNReal.ofReal_mul hk.le, show -γ + x = x - γ by abel]
  rw [sqrt_inverse_norm_sq S hS hA]
  congr 1
  simp only [weight, exponent, inner_zero_left, zero_sub]
  rw [show -⟪x - γ, matrixCLM S⁻¹ (x - γ)⟫ / 2 =
      -(1 / 2 * ⟪x - γ, matrixCLM S⁻¹ (x - γ)⟫) by ring]
  ring

theorem gaussianLaw_absolutelyContinuous (S : Covariance d) (hS : S.PosDef) (γ : Space d) :
    gaussianLaw S γ ≪ volume := by
  obtain ⟨c, _, hc⟩ := gaussianDensityFormula S hS
  rw [hc γ]
  exact withDensity_absolutelyContinuous _ _

/-- Strict positivity of the Gaussian density also gives the reverse absolute continuity. -/
theorem volume_absolutelyContinuous_gaussianLaw
    (S : Covariance d) (hS : S.PosDef) (γ : Space d) :
    volume ≪ gaussianLaw S γ := by
  obtain ⟨c, hc, hformula⟩ := gaussianDensityFormula S hS
  rw [hformula γ]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · apply Measurable.aemeasurable
    unfold weight exponent
    fun_prop
  · exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr
      (mul_pos hc (Real.exp_pos (exponent S 0 (x - γ))))).ne'

theorem gaussianLaw_null_iff (S : Covariance d) (hS : S.PosDef) (γ : Space d)
    (O : Set (Space d)) : gaussianLaw S γ O = 0 ↔ volume O = 0 :=
  ⟨fun h => volume_absolutelyContinuous_gaussianLaw S hS γ h,
    fun h => gaussianLaw_absolutelyContinuous S hS γ h⟩

theorem gaussianLaw_mass_pos (S : Covariance d) (hS : S.PosDef) (γ : Space d)
    (O : Set (Space d)) (hO : IsOpen O) (hne : O.Nonempty) :
    0 < gaussianLaw S γ O := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  exact (hO.measure_pos volume hne).ne' ((gaussianLaw_null_iff S hS γ O).mp hzero)

end MajorityDynamics.Analysis.ConditionalGaussian
