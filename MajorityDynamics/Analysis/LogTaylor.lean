import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Explicit logarithmic Taylor bounds used in A.2 -/

namespace MajorityDynamics.Analysis

theorem log_one_add_linear_error {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  norm_num [Finset.sum_range_succ, sub_neg_eq_add] at h
  have heq : -x + Real.log (1 + x) = Real.log (1 + x) - x := by ring
  rw [heq] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - |x|)).mpr
  nlinarith [sq_abs x, mul_le_mul_of_nonneg_left hx (sq_nonneg x)]

theorem log_one_add_quadratic_error {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x + x ^ 2 / 2| ≤ 2 * |x| ^ 3 := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 2
  norm_num [Finset.sum_range_succ, sub_neg_eq_add] at h
  have heq : -x + x ^ 2 / 2 + Real.log (1 + x) = Real.log (1 + x) - x + x ^ 2 / 2 := by ring
  rw [heq] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - |x|)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hx (pow_nonneg (abs_nonneg x) 3)]

end MajorityDynamics.Analysis
