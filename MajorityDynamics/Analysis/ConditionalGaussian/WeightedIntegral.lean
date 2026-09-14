import MajorityDynamics.Analysis.ConditionalGaussian.Partition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth polynomially weighted partition integrals

Polynomial moment bounds and local domination justify differentiation under
the integral. Repeated differentiation multiplies the integrand by a linear
functional, preserving polynomial growth, and hence gives smoothness.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Matrix RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

private theorem growth_nonneg {f : Space d → ℝ}
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n := by
  obtain ⟨C, n, hC⟩ := hgrowth
  refine ⟨|C|, abs_nonneg C, n, fun x => (hC x).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (norm_nonneg x) n)

private theorem growth_mul_inner {f : Space d → ℝ}
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n)
    (y : Space d) :
    ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x * ⟪x, y⟫‖ ≤ C * ‖x‖ ^ n := by
  obtain ⟨C, hC, n, hbound⟩ := growth_nonneg hgrowth
  refine ⟨C * ‖y‖, n + 1, ?_⟩
  intro x
  calc
    ‖f x * ⟪x, y⟫‖ = ‖f x‖ * ‖⟪x, y⟫‖ := norm_mul _ _
    _ ≤ (C * ‖x‖ ^ n) * (‖x‖ * ‖y‖) :=
      mul_le_mul (hbound x) (norm_inner_le_norm x y) (norm_nonneg _)
        (mul_nonneg hC (pow_nonneg (norm_nonneg x) n))
    _ = C * ‖y‖ * ‖x‖ ^ (n + 1) := by rw [pow_succ]; ring

private theorem weighted_integrand_hasFDerivAt
    (S : Covariance d) (f : Space d → ℝ) (θ x : Space d) :
    HasFDerivAt (fun η => f x * weight S η x)
      ((f x * weight S θ x) • innerSL ℝ x) θ := by
  have h := (((innerSL ℝ x).hasFDerivAt (x := θ)).sub_const
    ((1 / 2 : ℝ) * ⟪x, matrixCLM S⁻¹ x⟫)).exp.const_mul (f x)
  simpa only [weight, exponent, innerSL_apply_apply, real_inner_comm x,
    smul_smul] using h

private theorem norm_weighted_derivative (S : Covariance d) (f : Space d → ℝ)
    (θ x : Space d) :
    ‖(f x * weight S θ x) • innerSL ℝ x‖ = ‖f x‖ * weight S θ x * ‖x‖ := by
  rw [norm_smul, norm_mul, innerSL_apply_norm,
    Real.norm_of_nonneg (show 0 ≤ weight S θ x from (Real.exp_pos _).le)]

section MomentDomination

variable {S : Covariance d} {O : Set (Space d)}
  (hmom : ∀ θ n, Integrable (fun x => ‖x‖ ^ n * weight S θ x) (volume.restrict O))
  (hdom : LocalDomination S O)

include hmom

/-- Polynomial growth suffices for integrability against each weighted law. -/
theorem integrable_mul_weight_of_moments {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n)
    (θ : Space d) :
    Integrable (fun x => f x * weight S θ x) (volume.restrict O) := by
  obtain ⟨C, n, hbound⟩ := hgrowth
  apply ((hmom θ n).const_mul C).mono' (hf.mul (continuous_weight S θ)).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖f x * weight S θ x‖ ≤ C * (‖x‖ ^ n * weight S θ x)
  rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ weight S θ x from (Real.exp_pos _).le)]
  calc
    ‖f x‖ * weight S θ x ≤ (C * ‖x‖ ^ n) * weight S θ x :=
      mul_le_mul_of_nonneg_right (hbound x) (Real.exp_pos _).le
    _ = C * (‖x‖ ^ n * weight S θ x) := mul_assoc _ _ _

/-- The operator-valued derivative integrand is also integrable. -/
theorem integrable_weighted_derivative_of_moments {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n)
    (θ : Space d) :
    Integrable (fun x => (f x * weight S θ x) • innerSL ℝ x) (volume.restrict O) := by
  obtain ⟨C, n, hbound⟩ := hgrowth
  apply ((hmom θ (n + 1)).const_mul C).mono'
    ((hf.mul (continuous_weight S θ)).smul (innerSL ℝ).continuous).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖(f x * weight S θ x) • innerSL ℝ x‖ ≤ C * (‖x‖ ^ (n + 1) * weight S θ x)
  rw [norm_weighted_derivative]
  calc
    ‖f x‖ * weight S θ x * ‖x‖ ≤ (C * ‖x‖ ^ n) * weight S θ x * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hbound x) (weight_pos S θ x).le) (norm_nonneg x)
    _ = C * (‖x‖ ^ (n + 1) * weight S θ x) := by rw [pow_succ]; ring

include hdom

/-- Differentiation under the integral using polynomial moment bounds and
domination on a neighborhood of the natural parameter. -/
theorem hasFDerivAt_weightedIntegral_of_domination {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n)
    (θ : Space d) :
    HasFDerivAt (fun η => ∫ x in O, f x * weight S η x)
      (∫ x in O, (f x * weight S θ x) • innerSL ℝ x) θ := by
  obtain ⟨C, hC, n, hbound⟩ := growth_nonneg hgrowth
  obtain ⟨ε, hε, bound, hbint, hbound'⟩ := hdom θ (n + 1)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds θ hε)
    (F := fun η x => f x * weight S η x)
    (F' := fun η x => (f x * weight S η x) • innerSL ℝ x)
    (Eventually.of_forall (fun η => (hf.mul (continuous_weight S η)).aestronglyMeasurable))
    (integrable_mul_weight_of_moments hmom hf hgrowth θ)
    ((hf.mul (continuous_weight S θ)).smul (innerSL ℝ).continuous).aestronglyMeasurable
    (bound := fun x => C * bound x) ?_ (hbint.const_mul C) ?_
  · apply ae_of_all
    intro x η hη
    rw [norm_weighted_derivative]
    calc
      ‖f x‖ * weight S η x * ‖x‖ ≤ (C * ‖x‖ ^ n) * weight S η x * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbound x) (weight_pos S η x).le) (norm_nonneg x)
      _ = C * (‖x‖ ^ (n + 1) * weight S η x) := by rw [pow_succ]; ring
      _ ≤ C * bound x := mul_le_mul_of_nonneg_left (hbound' η hη x) hC
  · exact ae_of_all _ fun x η _ => weighted_integrand_hasFDerivAt S f η x

/-- All orders follow by induction: applying the integral derivative to a
vector multiplies the scalar integrand by another linear functional. -/
theorem contDiff_weightedIntegral_of_domination {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) :
    ContDiff ℝ ∞ (fun θ => ∫ x in O, f x * weight S θ x) := by
  apply contDiff_infty.mpr
  intro k
  induction k generalizing f with
  | zero =>
      apply contDiff_zero.mpr
      exact continuous_iff_continuousAt.mpr (fun θ =>
        (hasFDerivAt_weightedIntegral_of_domination hmom hdom hf hgrowth θ).continuousAt)
  | succ k ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun θ => ∫ x in O, (f x * weight S θ x) • innerSL ℝ x, ?_,
        hasFDerivAt_weightedIntegral_of_domination hmom hdom hf hgrowth⟩
      apply contDiff_clm_apply_iff.mpr
      intro y
      have hy := ih (hf.mul (continuous_id.inner continuous_const)) (growth_mul_inner hgrowth y)
      convert hy using 1
      ext θ
      rw [ContinuousLinearMap.integral_apply
        (integrable_weighted_derivative_of_moments hmom hf hgrowth θ) y]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp only [smul_apply,
        innerSL_apply_apply, smul_eq_mul, Pi.mul_apply, id_eq]; ring

end MomentDomination

/-- Polynomially weighted Gaussian integrands are integrable on every set. -/
theorem integrable_mul_weight {S : Covariance d} (hS : S.PosDef) (O : Set (Space d))
    {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) (θ : Space d) :
    Integrable (fun x => f x * weight S θ x) (volume.restrict O) :=
  integrable_mul_weight_of_moments (integrable_weighted_moment hS O) hf hgrowth θ

/-- The operator-valued first derivative is integrable. -/
theorem integrable_weighted_derivative {S : Covariance d} (hS : S.PosDef)
    (O : Set (Space d)) {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) (θ : Space d) :
    Integrable (fun x => (f x * weight S θ x) • innerSL ℝ x) (volume.restrict O) :=
  integrable_weighted_derivative_of_moments (integrable_weighted_moment hS O) hf hgrowth θ

/-- Fréchet differentiation of a polynomially weighted partition integral. -/
theorem hasFDerivAt_weightedIntegral {S : Covariance d} (hS : S.PosDef)
    (O : Set (Space d)) {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) (θ : Space d) :
    HasFDerivAt (fun η => ∫ x in O, f x * weight S η x)
      (∫ x in O, (f x * weight S θ x) • innerSL ℝ x) θ :=
  hasFDerivAt_weightedIntegral_of_domination (integrable_weighted_moment hS O)
    (localDomination hS O) hf hgrowth θ

/-- Every continuous polynomial multiplier has a smooth weighted partition integral. -/
theorem contDiff_weightedIntegral {S : Covariance d} (hS : S.PosDef)
    (O : Set (Space d)) {f : Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) :
    ContDiff ℝ ∞ (fun θ => ∫ x in O, f x * weight S θ x) :=
  contDiff_weightedIntegral_of_domination (integrable_weighted_moment hS O)
    (localDomination hS O) hf hgrowth

end MajorityDynamics.Analysis.ConditionalGaussian
