import MajorityDynamics.Combinatorics.DegreeRatios.LogBounds

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

/-- Uniform control of the empirical-density substitution. The explicit
constant is independent of the capacity, degree, and density. -/
theorem density_error_bound {n p u d h q t K L : ℝ}
    (hn : 0 ≤ n) (hp : 0 < p) (hp1 : p ≤ 1) (hu : u = p * n)
    (hd0 : 0 ≤ d) (hdh : d ≤ h) (hhn : h ≤ n) (hdu : d ≤ 2 * u)
    (hcenter : |h * p - u| ≤ p) (hdegree : |d - u| ≤ Real.sqrt u * L)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (ht : |t| ≤ 1 / 2)
    (hrelative : Real.sqrt u * |t| ≤ K)
    (hq : q = p * (1 + t)) (hqsmall : |q| ≤ 1 / 2)
    (hsparse : n * p ^ 2 ≤ 1) :
    |(-d * Real.log q - (h - d) * Real.log (1 - q)) +
        d * Real.log p - u| ≤ K * L + 4 * K ^ 2 + 10 := by
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hs := Real.sq_sqrt hu0
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact mul_nonneg hp.le (by linarith [(abs_le.mp ht).1])
  have hqu : q ≤ 3 / 2 * p := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp ht).2 hp.le
    rw [hq]
    nlinarith
  have h1 : |d - u| * |t| ≤ K * L := by
    calc
      _ ≤ (Real.sqrt u * L) * |t| := mul_le_mul_of_nonneg_right hdegree (abs_nonneg _)
      _ = (Real.sqrt u * |t|) * L := by ring
      _ ≤ K * L := mul_le_mul_of_nonneg_right hrelative (by linarith)
  have h2 : |h * p - u| * |1 + t| ≤ 2 := by
    have hab : |1 + t| ≤ 3 / 2 := by
      calc
        _ ≤ |(1 : ℝ)| + |t| := abs_add_le _ _
        _ ≤ 3 / 2 := by simpa only [abs_one] using (show 1 + |t| ≤ 3 / 2 by linarith)
    have hh := mul_le_mul hcenter hab (abs_nonneg _) hp.le
    nlinarith
  have h3 : |d * q| ≤ 3 := by
    rw [abs_of_nonneg (mul_nonneg hd0 hq0)]
    have hh := mul_le_mul hdu hqu hq0 (by positivity : 0 ≤ 2 * u)
    rw [hu] at hh
    nlinarith
  have h4 : 2 * |d| * t ^ 2 ≤ 4 * K ^ 2 := by
    rw [abs_of_nonneg hd0]
    have hab : (Real.sqrt u * |t|) ^ 2 ≤ K ^ 2 :=
      (sq_le_sq₀ (by positivity) hK).mpr hrelative
    rw [mul_pow, hs, sq_abs] at hab
    have hh := mul_le_mul_of_nonneg_right hdu (sq_nonneg t)
    nlinarith
  have h5 : 2 * |h - d| * q ^ 2 ≤ 5 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hdh)]
    have hh : h - d ≤ n := by linarith
    have hsq : q ^ 2 ≤ (3 / 2 * p) ^ 2 :=
      (sq_le_sq₀ hq0 (by positivity)).mpr hqu
    have he := mul_le_mul hh hsq (sq_nonneg q) hn
    nlinarith
  exact (density_cancellation hp hq ht hqsmall).trans (by linarith)

end MajorityDynamics.Combinatorics.DegreeRatios
