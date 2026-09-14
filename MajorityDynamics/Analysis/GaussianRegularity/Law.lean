import MajorityDynamics.Analysis.GaussianRegularity.Basic
import MajorityDynamics.Analysis.GaussianRegularity.Density
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The diagonal multivariate Gaussian is the actual product Gaussian, and has
its standard product density with respect to Euclidean volume. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace BigOperators NNReal ENNReal
namespace MajorityDynamics.Analysis.GaussianRegularity
open ConditionalGaussian
variable {d : ℕ}

theorem map_product_gaussian (m : Space d) (v : Fin d → ℝ≥0) :
    (Measure.pi fun i => gaussianReal (m i) (v i)).map (WithLp.toLp 2) =
      gaussianLaw (Matrix.diagonal (fun i => (v i : ℝ))) m := by
  unfold gaussianLaw
  apply Measure.ext_of_charFun (E := Space d)
  ext t
  rw [charFun_multivariateGaussian (Matrix.PosSemidef.diagonal (fun i => (v i).coe_nonneg))]
  simp_rw [charFun_pi, charFun_gaussianReal, ← Complex.exp_sum]
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec_diagonal,
    star_trivial, Complex.ofReal_sum, Finset.sum_sub_distrib,
    Finset.sum_div, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> push_cast <;> ring

private theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    setLIntegral_map (f := fun y => f (e.symm y)) hs
      (hf.comp e.symm.measurable) e.measurable]
  simp

theorem product_gaussian_density (m : Fin d → ℝ) (v : Fin d → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) :
    (Measure.pi fun i => gaussianReal (m i) (v i)) =
      volume.withDensity (fun x : Fin d → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (m i) (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x in Set.univ.pi s,
    ENNReal.ofReal (∏ i, gaussianPDFReal (m i) (v i) (x i))
    ∂(Measure.pi fun _ : Fin d => volume)) = _
  rw [Measure.restrict_pi_pi, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_fintype_prod_eq_prod]
    simp_rw [gaussianReal_apply_eq_integral _ (hv _)]
    exact ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg fun x =>
      gaussianPDFReal_nonneg _ _ x
  · exact Integrable.fintype_prod fun i => (integrable_gaussianPDFReal (m i) (v i)).restrict
  · exact ae_of_all _ fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ (x i)

theorem diagonal_gaussian_density (m : Space d) (v : Fin d → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) :
    gaussianLaw (Matrix.diagonal (fun i => (v i : ℝ))) m =
      volume.withDensity (fun x : Space d =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (m i) (v i) (x i))) := by
  rw [← map_product_gaussian m v, product_gaussian_density _ v hv]
  change Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) _ = _
  rw [map_withDensity_equiv]
  · rw [show Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) volume = volume from
      (PiLp.volume_preserving_toLp (Fin d)).map_eq]
    rfl
  · fun_prop

/-- The density bridge in the actual real-variance parameter convention. -/
theorem law_withDensity {r : ℕ} (p : Parameters d r) (hv : positiveVariance p) :
    law p = volume.withDensity (fun x : Space d =>
      ENNReal.ofReal (∏ i, gaussianPDFReal (p.1.1 i) (Real.toNNReal (p.1.2 i)) (x i))) := by
  have heq : (fun i => (Real.toNNReal (p.1.2 i) : ℝ)) = fun i => p.1.2 i := by
    funext i
    exact Real.coe_toNNReal _ (hv i).le
  have h := diagonal_gaussian_density p.1.1 (fun i => Real.toNNReal (p.1.2 i))
    (fun i => ne_of_gt (Real.toNNReal_pos.mpr (hv i)))
  simpa only [heq, law] using h

/-- Integrals over the real Gaussian equal density integrals, without a
separate integrability premise (both sides use the Bochner convention). -/
theorem setIntegral_law_density {r : ℕ} (p : Parameters d r) (hv : positiveVariance p)
    (O : Set (Space d)) (f : Space d → ℝ) :
    ∫ x in O, f x ∂law p = ∫ x in O,
      (∏ i, gaussianPDFReal (p.1.1 i) (Real.toNNReal (p.1.2 i)) (x i)) * f x := by
  rw [law_withDensity p hv, restrict_withDensity']
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _)]
      rfl
  · fun_prop
  · exact ae_of_all _ fun _ => ENNReal.ofReal_lt_top

/-- Real-coordinate density formula used by the parameter estimates. -/
theorem setIntegral_law_eq_density {r : ℕ} (p : Parameters d r) (hv : positiveVariance p)
    (O : Set (Space d)) (f : Space d → ℝ) :
    ∫ x in O, f x ∂law p = ∫ x in O, density p.1.1 p.1.2 x * f x := by
  rw [setIntegral_law_density p hv]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only [density]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [scalarDensity, gaussianPDFReal, Real.coe_toNNReal _ (hv i).le]

end MajorityDynamics.Analysis.GaussianRegularity
