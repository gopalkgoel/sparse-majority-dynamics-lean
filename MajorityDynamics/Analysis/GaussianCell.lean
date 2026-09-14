import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Gaussian density and mass comparison on unit cells -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace MajorityDynamics.Analysis

theorem gaussian_real_eq_integral (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (S : Set ℝ) :
    (gaussianReal m v).real S = ∫ y in S, gaussianPDFReal m v y := by
  rw [measureReal_def, gaussianReal_apply_eq_integral m hv,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg m v))]

theorem gaussian_pdf_cell_error (m : ℝ) (v : ℝ≥0) (hv : 0 < v) (x y R : ℝ)
    (_hR : 0 ≤ R) (hx : |x - m| ≤ R) (hxy : |y - x| ≤ 1)
    (hsmall : (2 * R + 1) / (2 * (v : ℝ)) ≤ 1) :
    |gaussianPDFReal m v y - gaussianPDFReal m v x| ≤
      2 * ((2 * R + 1) / (2 * (v : ℝ))) * gaussianPDFReal m v x := by
  have hv0 : (0 : ℝ) < v := hv
  let z := ((x - m) ^ 2 - (y - m) ^ 2) / (2 * (v : ℝ))
  have hz : |z| ≤ (2 * R + 1) / (2 * (v : ℝ)) := by
    dsimp [z]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * (v : ℝ))]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hid : (x - m) ^ 2 - (y - m) ^ 2 = -(y - x) * (2 * (x - m) + (y - x)) := by ring
    rw [hid, abs_mul, abs_neg]
    have hs : |2 * (x - m) + (y - x)| ≤ 2 * R + 1 := by
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    nlinarith [mul_le_mul hxy hs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hid : gaussianPDFReal m v y = gaussianPDFReal m v x * Real.exp z := by
    simp only [gaussianPDFReal]
    rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
    congr 2
    dsimp [z]
    ring
  rw [hid, ← mul_sub_one, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg m v x)]
  have he := Real.abs_exp_sub_one_le (hz.trans hsmall)
  have h := mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left hz (by norm_num)))
    (gaussianPDFReal_nonneg m v x)
  nlinarith only [h]

/-- The actual Gaussian probability of a unit interval is relatively close
to the density at its lattice endpoint. -/
theorem gaussian_cell_mass_error (m : ℝ) (v : ℝ≥0) (hv : 0 < v) (x R : ℝ)
    (hR : 0 ≤ R) (hx : |x - m| ≤ R)
    (hsmall : (2 * R + 1) / (2 * (v : ℝ)) ≤ 1) :
    |(gaussianReal m v).real (Ico x (x + 1)) - gaussianPDFReal m v x| ≤
      2 * ((2 * R + 1) / (2 * (v : ℝ))) * gaussianPDFReal m v x := by
  have hc : volume.real (Ico x (x + 1)) = 1 := by simp
  have hconst : (∫ _y in Ico x (x + 1), gaussianPDFReal m v x) = gaussianPDFReal m v x := by
    rw [setIntegral_const, smul_eq_mul, hc, one_mul]
  conv_lhs => rw [gaussian_real_eq_integral m v hv.ne', ← hconst,
    ← integral_sub (integrable_gaussianPDFReal m v).integrableOn (integrableOn_const (by simp))]
  calc
    _ ≤ ∫ y in Ico x (x + 1), |gaussianPDFReal m v y - gaussianPDFReal m v x| := abs_integral_le_integral_abs
    _ ≤ ∫ _y in Ico x (x + 1), 2 * ((2 * R + 1) / (2 * (v : ℝ))) * gaussianPDFReal m v x := by
      apply integral_mono_ae
        ((integrable_gaussianPDFReal m v).integrableOn.sub (integrableOn_const (by simp))).abs
        (integrableOn_const (by simp))
      filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
      apply gaussian_pdf_cell_error m v hv x y R hR hx _ hsmall
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
      linarith [hy.2]
    _ = _ := by rw [setIntegral_const, smul_eq_mul, hc, one_mul]

end MajorityDynamics.Analysis
