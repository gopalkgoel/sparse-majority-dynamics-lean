import MajorityDynamics.Analysis.ConditionalGaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Raw partition bounds for conditioned Gaussian exponential families

All bounds in this file concern volume integrals. In particular, none use a
Gaussian density identification or a conditional-mean theorem.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

@[fun_prop]
theorem continuous_exponent (S : Covariance d) (θ : Space d) :
    Continuous (exponent S θ) := by
  unfold exponent
  fun_prop

@[fun_prop]
theorem continuous_weight (S : Covariance d) (θ : Space d) :
    Continuous (weight S θ) := (continuous_exponent S θ).rexp

@[simp]
theorem weight_pos (S : Covariance d) (θ x : Space d) : 0 < weight S θ x :=
  Real.exp_pos _

theorem inner_matrixCLM_pos {S : Covariance d} (hS : S.PosDef) {x : Space d}
    (hx : x ≠ 0) : 0 < ⟪x, matrixCLM S x⟫ := by
  have hx' : x.ofLp ≠ 0 := by
    intro h
    apply hx
    exact (WithLp.ofLp_injective 2) h
  simpa only [matrixCLM, Matrix.inner_toEuclideanCLM, star_trivial] using
    hS.dotProduct_mulVec_pos hx'

/-- A positive quadratic form has a uniform positive lower bound on the unit sphere.
The argument also covers the zero-dimensional space, whose unit sphere is empty. -/
theorem exists_quadratic_lower (A : Space d →L[ℝ] Space d)
    (hA : ∀ x ≠ 0, 0 < ⟪x, A x⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, A x⟫ := by
  have hunit : ∀ x : Space d, x ≠ 0 → ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Space d) 1 := by
    intro x hx
    simp [norm_smul, norm_inv, norm_ne_zero_iff.mpr hx]
  by_cases hs : (Metric.sphere (0 : Space d) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Space d) 1).exists_isMinOn hs
      (show ContinuousOn (fun x : Space d => ⟪x, A x⟫) _ from
        (continuous_id.inner A.continuous).continuousOn)
    have hun : u ≠ 0 := by
      intro h
      simp [h] at hu
    refine ⟨⟪u, A u⟫, hA u hun, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have heq : ‖x‖ • (‖x‖⁻¹ • x) = x := smul_inv_smul₀ hn x
    calc
      ⟪u, A u⟫ * ‖x‖ ^ 2 ≤ ⟪‖x‖⁻¹ • x, A (‖x‖⁻¹ • x)⟫ * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hmin (hunit x hx)) (sq_nonneg _)
      _ = ⟪x, A x⟫ := by
        conv_rhs => rw [← heq]
        simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hx : x = 0 := by
      by_contra hx
      exact hs ⟨_, hunit x hx⟩
    simp [hx]

/-- The inverse covariance controls the Euclidean norm in every direction. -/
theorem inverse_quadratic_lower {S : Covariance d} (hS : S.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, matrixCLM S⁻¹ x⟫ :=
  exists_quadratic_lower _ (fun _ hx => inner_matrixCLM_pos hS.inv hx)

/-- A scalar Gaussian envelope, directly with respect to volume. -/
theorem integrable_gaussian_envelope {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Space d => Real.exp (-c * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Space d) (b := (c : ℂ)) (by simpa using hc) 0 0).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

private theorem linear_quadratic_bound {c : ℝ} (hc : 0 < c) (R r : ℝ) :
    R * r - c / 4 * r ^ 2 ≤ R ^ 2 / c := by
  apply (le_div_iff₀ hc).mpr
  nlinarith [sq_nonneg (c * r - 2 * R)]

/-- All polynomial moments and all parameters in a bounded set share one
integrable Gaussian envelope. -/
theorem bounded_parameter_domination {S : Covariance d} (hS : S.PosDef)
    (R : ℝ) (n : ℕ) :
    ∃ bound : Space d → ℝ, Integrable bound ∧
      ∀ θ, ‖θ‖ ≤ R → ∀ x, ‖x‖ ^ n * weight S θ x ≤ bound x := by
  obtain ⟨c, hc, hq⟩ := inverse_quadratic_lower hS
  let C := (n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / c)
  refine ⟨fun x => C * Real.exp (-(c / 4) * ‖x‖ ^ 2),
    (integrable_gaussian_envelope (by positivity : 0 < c / 4)).const_mul C, ?_⟩
  intro θ hθ x
  have hp : ‖x‖ ^ n ≤ (n.factorial : ℝ) * Real.exp ‖x‖ := by
    have hf : (0 : ℝ) < n.factorial := by positivity
    exact (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp _ (norm_nonneg _) n) |>.trans_eq (mul_comm _ _)
  have hinner : ⟪θ, x⟫ ≤ R * ‖x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))
  have he : ‖x‖ + exponent S θ x ≤ (R + 1) ^ 2 / c - c / 4 * ‖x‖ ^ 2 := by
    have hb := linear_quadratic_bound hc (R + 1) ‖x‖
    have hqx := hq x
    unfold exponent
    nlinarith
  calc
    ‖x‖ ^ n * weight S θ x ≤
        ((n.factorial : ℝ) * Real.exp ‖x‖) * Real.exp (exponent S θ x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * Real.exp (‖x‖ + exponent S θ x) := by rw [Real.exp_add]; ring
    _ ≤ (n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / c - c / 4 * ‖x‖ ^ 2) := by
      gcongr
    _ = C * Real.exp (-(c / 4) * ‖x‖ ^ 2) := by
      dsimp [C]
      simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

/-- Every raw polynomially weighted moment is finite, with no boundedness
assumption on the conditioning set. -/
theorem integrable_weighted_moment {S : Covariance d} (hS : S.PosDef)
    (O : Set (Space d)) (θ : Space d) (n : ℕ) :
    Integrable (fun x => ‖x‖ ^ n * weight S θ x) (volume.restrict O) := by
  obtain ⟨bound, hb, hbound⟩ := bounded_parameter_domination hS ‖θ‖ n
  apply hb.restrict.mono' ((continuous_norm.pow n).mul (continuous_weight S θ)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖‖x‖ ^ n * weight S θ x‖ ≤ bound x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (weight_pos S θ x).le)]
    exact hbound θ le_rfl x

theorem integrable_weight {S : Covariance d} (hS : S.PosDef)
    (O : Set (Space d)) (θ : Space d) :
    Integrable (weight S θ) (volume.restrict O) := by
  simpa using integrable_weighted_moment hS O θ 0

/-- Domination is uniform on a fixed neighborhood of each natural parameter. -/
theorem localDomination {S : Covariance d} (hS : S.PosDef)
    (O : Set (Space d)) : LocalDomination S O := by
  intro θ₀ n
  obtain ⟨bound, hb, hbound⟩ := bounded_parameter_domination hS (‖θ₀‖ + 1) n
  refine ⟨1, zero_lt_one, bound, hb.restrict, ?_⟩
  intro θ hθ x
  apply hbound θ _ x
  have hd : ‖θ - θ₀‖ < 1 := by simpa [dist_eq_norm] using hθ
  have hh := norm_add_le (θ - θ₀) θ₀
  simpa using (hh.trans (by linarith : ‖θ - θ₀‖ + ‖θ₀‖ ≤ ‖θ₀‖ + 1))

/-- A nonempty open conditioning set has nonzero restricted volume. -/
theorem restrictedVolume_neZero {O : Set (Space d)} (hne : O.Nonempty) (hO : IsOpen O) :
    NeZero (volume.restrict O) :=
  ⟨fun h => (hO.measure_pos volume hne).ne' (Measure.restrict_eq_zero.mp h)⟩

/-- The raw partition function is strictly positive. -/
theorem partition_pos {S : Covariance d} (hS : S.PosDef) {O : Set (Space d)}
    (hne : O.Nonempty) (hO : IsOpen O) (θ : Space d) : 0 < partition S O θ := by
  have := restrictedVolume_neZero hne hO
  exact integral_exp_pos (integrable_weight hS O θ)

/-- The natural law is a probability measure with second moments, supported on
`O` and absolutely continuous with respect to volume. -/
theorem natural_regular {S : Covariance d} (hS : S.PosDef) {O : Set (Space d)}
    (hne : O.Nonempty) (hO : IsOpen O) (θ : Space d) : RegularOn (naturalLaw S O θ) O := by
  have := restrictedVolume_neZero hne hO
  have hw := integrable_weight hS O θ
  have hp : IsProbabilityMeasure (naturalLaw S O θ) := isProbabilityMeasure_tilted hw
  have hac : naturalLaw S O θ ≪ volume.restrict O := tilted_absolutelyContinuous _ _
  refine ⟨hp, ?_, ?_, hac.trans Measure.absolutelyContinuous_restrict⟩
  · apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr
    apply (integrable_tilted_iff hw _).mpr
    simpa only [id_eq, weight, smul_eq_mul, mul_comm] using
      integrable_weighted_moment hS O θ 2
  · have hz : naturalLaw S O θ Oᶜ = 0 := hac (by
      rw [Measure.restrict_apply hO.measurableSet.compl]
      simp)
    simpa only [hz, add_zero] using (prob_add_prob_compl (μ := naturalLaw S O θ) hO.measurableSet)

/-- Complete raw partition and normalized-measure facts. Convexity is not needed
for these estimates. -/
theorem partitionFacts {S : Covariance d} (hS : S.PosDef) {O : Set (Space d)}
    (hne : O.Nonempty) (hO : IsOpen O) : PartitionFacts S O where
  integrable_weight := integrable_weight hS O
  partition_pos := partition_pos hS hne hO
  weighted_moments := integrable_weighted_moment hS O
  natural_regular := natural_regular hS hne hO

end MajorityDynamics.Analysis.ConditionalGaussian
