import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

/-- A first-order bound suitable for a short factorial product. -/
theorem abs_log_one_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * |x| := by
  have h := Real.abs_log_sub_add_sum_range_le
    (lt_of_le_of_lt hx (by norm_num : (1 / 2 : ℝ) < 1)) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one] at h
  apply h.trans
  calc
    |x| / (1 - |x|) ≤ |x| / (1 / 2) :=
      div_le_div_of_nonneg_left (abs_nonneg x) (by norm_num) (by linarith)
    _ = 2 * |x| := by ring

/-- A quadratic remainder uniform on the closed half-unit interval. -/
theorem abs_log_one_sub_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (lt_of_le_of_lt hx (by norm_num : (1 / 2 : ℝ) < 1)) 1
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    zero_add, Nat.cast_zero, div_one, pow_one, Nat.reduceAdd] at h
  rw [add_comm] at h
  apply h.trans
  calc
    |x| ^ 2 / (1 - |x|) ≤ |x| ^ 2 / (1 / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
    _ = 2 * x ^ 2 := by rw [sq_abs]; ring

/-- The cancellation needed after replacing the empirical density by `p`.
This finite identity separates the linear cancellation from the two Taylor
remainders; its hypotheses will be supplied by the uniform windows. -/
theorem density_cancellation {p q u d h t : ℝ}
    (hp : 0 < p) (hqt : q = p * (1 + t))
    (ht : |t| ≤ 1 / 2) (hqsmall : |q| ≤ 1 / 2) :
    |(-d * Real.log q - (h - d) * Real.log (1 - q)) +
        d * Real.log p - u| ≤
      |d - u| * |t| + |h * p - u| * |1 + t| + |d * q| +
        2 * |d| * t ^ 2 + 2 * |h - d| * q ^ 2 := by
  have htpos : 0 < 1 + t := by linarith [(abs_le.mp ht).1]
  have hlog : Real.log q = Real.log p + Real.log (1 + t) := by
    rw [hqt, Real.log_mul hp.ne' htpos.ne']
  have htaylor : |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
    have hh := abs_log_one_sub_add_le (x := -t) (by simpa only [abs_neg] using ht)
    simpa only [sub_eq_add_neg, neg_neg, neg_sq] using hh
  have hqtaylor := abs_log_one_sub_add_le hqsmall
  have hid : (-d * Real.log q - (h - d) * Real.log (1 - q)) +
      d * Real.log p - u =
      -(d - u) * t + (h * p - u) * (1 + t) - d * q -
        d * (Real.log (1 + t) - t) -
        (h - d) * (Real.log (1 - q) + q) := by
    rw [hlog, hqt]
    ring
  rw [hid]
  calc
    _ ≤ |-(d - u) * t + (h * p - u) * (1 + t) - d * q -
        d * (Real.log (1 + t) - t)| +
        |(h - d) * (Real.log (1 - q) + q)| := abs_sub _ _
    _ ≤ (|-(d - u) * t + (h * p - u) * (1 + t) - d * q| +
        |d * (Real.log (1 + t) - t)|) +
        |(h - d) * (Real.log (1 - q) + q)| := by gcongr; exact abs_sub _ _
    _ ≤ ((|-(d - u) * t + (h * p - u) * (1 + t)| + |d * q|) +
        |d * (Real.log (1 + t) - t)|) +
        |(h - d) * (Real.log (1 - q) + q)| := by gcongr; exact abs_sub _ _
    _ ≤ (((|-(d - u) * t| + |(h * p - u) * (1 + t)|) + |d * q|) +
        |d * (Real.log (1 + t) - t)|) +
        |(h - d) * (Real.log (1 - q) + q)| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_neg]
      have ha := mul_le_mul_of_nonneg_left htaylor (abs_nonneg d)
      have hb := mul_le_mul_of_nonneg_left hqtaylor (abs_nonneg (h - d))
      nlinarith

end MajorityDynamics.Combinatorics.DegreeRatios
