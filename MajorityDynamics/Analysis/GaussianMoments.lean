import MajorityDynamics.Analysis.GaussianLinear
import Mathlib.MeasureTheory.Integral.Pi

/-! # Uniform scalar Gaussian moment bounds via the standard normal -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace MajorityDynamics.Analysis

theorem integrable_gaussian_power (m : ℝ) (v : ℝ≥0) (D : ℕ) :
    Integrable (fun x : ℝ => x ^ D) (gaussianReal m v) :=
  integrable_pow_of_integrable_exp_mul one_ne_zero (integrable_exp_mul_gaussianReal 1)
    (integrable_exp_mul_gaussianReal (-1)) D

def normalMomentBound (T : ℝ) (D : ℕ) : ℝ :=
  ∫ z, (|z| + T) ^ D ∂gaussianReal 0 1

theorem integrable_normalMomentBound (T : ℝ) (D : ℕ) (hT : 0 ≤ T) :
    Integrable (fun z : ℝ => (|z| + T) ^ D) (gaussianReal 0 1) := by
  have hm : MemLp (fun z : ℝ => |z| + T) (D : ℝ≥0∞) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (D : ℝ≥0∞) (by simp)).norm.add (memLp_const T)
  have h := hm.integrable_norm_pow'
  simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg _) hT)] using h

theorem normalMomentBound_nonneg (T : ℝ) (D : ℕ) (hT : 0 ≤ T) :
    0 ≤ normalMomentBound T D := integral_nonneg fun z => pow_nonneg (by positivity) _

theorem standard_affine_gaussian (σ α : ℝ) :
    (gaussianReal 0 1).map (fun z => σ * (z + α)) =
      gaussianReal (σ * α) (NNReal.mk (σ ^ 2) (sq_nonneg _)) := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) σ
  have hh := gaussianReal_map_add_const (μ := σ * 0) (v := NNReal.mk (σ ^ 2) (sq_nonneg _) * 1) (σ * α)
  rw [← h, Measure.map_map (by fun_prop) (by fun_prop)] at hh
  simp only [mul_zero, zero_add, mul_one] at hh
  convert hh using 1
  congr 1
  ext z
  simp only [Function.comp_apply]
  ring

theorem gaussian_absolute_moment_le (σ α T : ℝ) (D : ℕ) (hσ : 0 ≤ σ) (hT : 0 ≤ T) (hα : |α| ≤ T) :
    (∫ x, |x| ^ D ∂gaussianReal (σ * α) (NNReal.mk (σ ^ 2) (sq_nonneg _))) ≤
      σ ^ D * normalMomentBound T D := by
  rw [← standard_affine_gaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, abs_of_nonneg hσ, mul_pow]
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hσ D)
  have hm : MemLp (fun z : ℝ => z + α) (D : ℝ≥0∞) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (D : ℝ≥0∞) (by simp)).add (memLp_const α)
  have hi : Integrable (fun z : ℝ => |z + α| ^ D) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs] using hm.integrable_norm_pow'
  apply integral_mono hi (integrable_normalMomentBound T D hT)
  intro z
  have hz : |z + α| ≤ |z| + T := (abs_add_le z α).trans (add_le_add le_rfl hα)
  exact pow_le_pow_left₀ (abs_nonneg _) hz _

end MajorityDynamics.Analysis
