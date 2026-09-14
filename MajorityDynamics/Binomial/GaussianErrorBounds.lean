import MajorityDynamics.Binomial.GaussianTiltBounds
import MajorityDynamics.Binomial.UniformWindow

/-! # Uniform sizes of the scalar Gaussian approximation errors -/

noncomputable section
namespace MajorityDynamics.Binomial.Approximation

theorem gaussian_step_error_bound (m : ℕ) (μ T n p s l : ℝ)
    (hT : 1 ≤ T) (hn : 0 < n) (hp : 0 < p) (hs : 0 < s) (hl : 1 ≤ l)
    (hscale : s ^ 2 = p * n) (hps : p * s ≤ 1)
    (hμ : s ^ 2 / T ≤ μ) (hrem : n / (2 * T) ≤ (m : ℝ) - μ) :
    2 * (s * l) * gaussianStepError m μ (s * l) ≤ 16 * T ^ 2 * l ^ 3 / s := by
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hμ0 : 0 < μ := (by positivity : 0 < s ^ 2 / T).trans_le hμ
  have _hrem0 : 0 < (m : ℝ) - μ := (by positivity : 0 < n / (2 * T)).trans_le hrem
  have hinv : 1 / ((m : ℝ) - μ) ≤ 2 * T / n := by
    simpa only [one_div_div, div_one] using one_div_le_one_div_of_le (show 0 < n / (2 * T) by positivity) hrem
  have hr : s * l / μ ≤ T * l / s := by
    have h := div_le_div_of_nonneg_left (show 0 ≤ s * l by positivity) (show 0 < s ^ 2 / T by positivity) hμ
    have heq : s * l / (s ^ 2 / T) = T * l / s := by
      field_simp
    exact h.trans_eq heq
  have hlin1 : 2 * (s * l) * (2 * (s * l) / ((m : ℝ) - μ)) ≤ 8 * T * l ^ 3 / s := by
    have h := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4 * (s * l) ^ 2 by positivity)
    have heq : 4 * (s * l) ^ 2 * (2 * T / n) = 8 * T * p * l ^ 2 := by
      rw [mul_pow, hscale]
      field_simp
      ring
    rw [heq] at h
    have hpl : p * l ^ 2 ≤ l ^ 3 / s := by
      apply (le_div_iff₀ hs).mpr
      have hh := mul_le_mul_of_nonneg_right hps (sq_nonneg l)
      nlinarith [mul_nonneg (sq_nonneg l) (show 0 ≤ l - 1 by linarith)]
    have hbound := mul_le_mul_of_nonneg_left hpl (show 0 ≤ 8 * T by positivity)
    simp only [div_eq_mul_inv] at h hbound ⊢
    nlinarith only [h, hbound]
  have hlin2 : 2 * (s * l) * (2 * (s * l / μ) ^ 2) ≤ 4 * T ^ 2 * l ^ 3 / s := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ s * l / μ) hr 2)
      (show 0 ≤ 4 * s * l by positivity)
    have heq : 4 * s * l * (T * l / s) ^ 2 = 4 * T ^ 2 * l ^ 3 / s := by field_simp
    rw [heq] at hh
    nlinarith only [hh]
  have hlin3 : 2 * (s * l) * (1 / (2 * μ)) ≤ T * l ^ 3 / s := by
    have hl3 : l ≤ l ^ 3 := by nlinarith [mul_nonneg (sq_nonneg l) (show 0 ≤ l - 1 by linarith)]
    have hh := mul_le_mul_of_nonneg_left hl3 hT0.le
    have h := hr.trans (div_le_div_of_nonneg_right hh hs.le)
    have heq : 2 * (s * l) * (1 / (2 * μ)) = s * l / μ := by ring
    rw [heq]
    exact h
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hbound : (8 * T + 4 * T ^ 2 + T) * l ^ 3 / s ≤ 16 * T ^ 2 * l ^ 3 / s := by
    apply div_le_div_of_nonneg_right _ hs.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  apply le_trans _ hbound
  unfold gaussianStepError
  simp only [div_eq_mul_inv] at hlin1 hlin2 hlin3 ⊢
  nlinarith only [hlin1, hlin2, hlin3]

theorem gaussian_scalar_geometry (m : ℕ) (p : Probability) (T n s l α : ℝ)
    (hT : 1 ≤ T) (hn : 0 < n) (hs : 0 < s) (hl : 8 * T ^ 2 ≤ l)
    (hscale : s ^ 2 = (p : ℝ) * n) (hsmall : (p : ℝ) ≤ 1 / 2)
    (hmlo : n / T ≤ m) (hmhi : (m : ℝ) ≤ T * n)
    (hlarge : 16 * T ^ 2 * l ≤ s) (hα : |α| ≤ T) :
    s ^ 2 / T ≤ (p : ℝ) * m ∧ (p : ℝ) * m ≤ T * s ^ 2 ∧
    n / (2 * T) ≤ (m : ℝ) - (p : ℝ) * m ∧
    s * l ≤ ((p : ℝ) * m) / 2 ∧
    Real.sqrt ((p : ℝ) * m) ≤ T * s ∧
    |α / Real.sqrt ((p : ℝ) * m)| ≤ 1 / 4 ∧
    |(m : ℝ) * (Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)) : ℝ) - (p : ℝ) * m| ≤ 4 * T ^ 2 * s ∧
    (m : ℝ) * (Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)) : ℝ) ≤ 2 * T * s ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hl0 : 0 ≤ l := (by positivity : 0 ≤ 8 * T ^ 2).trans hl
  have hm0 : (0 : ℝ) < m := (div_pos hn hT0).trans_le hmlo
  have hμ0 : 0 < (p : ℝ) * m := mul_pos p.property.1 hm0
  have hlo : s ^ 2 / T ≤ (p : ℝ) * m := by
    have h := mul_le_mul_of_nonneg_left hmlo p.property.1.le
    rw [← mul_div_assoc, ← hscale] at h
    exact h
  have hhi : (p : ℝ) * m ≤ T * s ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hmhi p.property.1.le
    rw [hscale]
    nlinarith only [h]
  have hrem : n / (2 * T) ≤ (m : ℝ) - (p : ℝ) * m := by
    have h := mul_le_mul_of_nonneg_right hsmall hm0.le
    have hnT : n / (2 * T) = (n / T) / 2 := by ring
    rw [hnT]
    linarith
  have hsl : 2 * T * l ≤ s := by nlinarith [mul_nonneg hl0 (show 0 ≤ 16 * T ^ 2 - 2 * T by nlinarith)]
  have hwindow : s * l ≤ ((p : ℝ) * m) / 2 := by
    have hh := (div_le_iff₀ hT0).mp hlo
    have h := mul_le_mul_of_nonneg_left hsl hs.le
    nlinarith
  have hsqrt := Real.sqrt_pos.mpr hμ0
  have hsquare := Real.sq_sqrt hμ0.le
  have hsqrtUpper : Real.sqrt ((p : ℝ) * m) ≤ T * s := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ T ^ 2 - T by nlinarith)]
  have hσ : 4 * T ≤ Real.sqrt ((p : ℝ) * m) := by
    have h := (div_le_iff₀ hT0).mp hlo
    have hslarge : 16 * T ^ 2 ≤ s := by nlinarith
    have hbound : 16 * T ^ 3 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 4 * T ^ 2)]
    nlinarith
  have ht : |α / Real.sqrt ((p : ℝ) * m)| ≤ 1 / 4 := by
    rw [abs_div, abs_of_pos hsqrt]
    apply (div_le_iff₀ hsqrt).mpr
    linarith
  have hlogit := gaussian_logistic_error p (α / Real.sqrt ((p : ℝ) * m)) ht
  have hshift : |(m : ℝ) * (Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)) : ℝ) - (p : ℝ) * m| ≤ 4 * T ^ 2 * s := by
    have hh := mul_le_mul_of_nonneg_left hlogit.1 hm0.le
    have heq : (m : ℝ) * (4 * (p : ℝ) * |α / Real.sqrt ((p : ℝ) * m)|) =
        4 * Real.sqrt ((p : ℝ) * m) * |α| := by
      rw [abs_div, abs_of_pos hsqrt]
      have hdiv : (p : ℝ) * m / Real.sqrt ((p : ℝ) * m) = Real.sqrt ((p : ℝ) * m) := by
        apply (div_eq_iff hsqrt.ne').mpr
        nlinarith only [hsquare]
      calc
        _ = 4 * |α| * ((p : ℝ) * m / Real.sqrt ((p : ℝ) * m)) := by ring
        _ = _ := by rw [hdiv]; ring
    rw [heq] at hh
    have hid : |(m : ℝ) * (Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)) : ℝ) - (p : ℝ) * m| =
        (m : ℝ) * |(Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)) : ℝ) - p| := by
      calc
        _ = |(m : ℝ) * ((Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)) : ℝ) - p)| := by congr 1; ring
        _ = _ := by rw [abs_mul, abs_of_pos hm0]
    rw [hid]
    apply hh.trans
    have h := mul_le_mul hsqrtUpper hα (abs_nonneg _) (by positivity : 0 ≤ T * s)
    nlinarith only [h]
  have hmean := mul_le_mul_of_nonneg_left hlogit.2 hm0.le
  exact ⟨hlo, hhi, hrem, hwindow, hsqrtUpper, ht, hshift, by nlinarith⟩

end MajorityDynamics.Binomial.Approximation
