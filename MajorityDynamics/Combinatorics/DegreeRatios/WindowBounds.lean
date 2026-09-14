import MajorityDynamics.Combinatorics.DegreeRatios.Uniform
import MajorityDynamics.Combinatorics.DegreeRatios.AnalyticError

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

/-- Numerical information needed to apply the finite-product bound. -/
structure RemovalBounds (T n p N m h d : ℝ) : Prop where
  capacity_pos : 0 < N
  count_pos : 0 < m
  count_lt : m < N
  degree_nonneg : 0 ≤ d
  degree_le : d ≤ h
  capacity_room : 2 * h ≤ N
  count_room : 2 * d ≤ m
  complement_room : 2 * (h - d) ≤ N - m
  capacity_error : h ^ 2 / N ≤ 4 * T
  count_error : d ^ 2 / m ≤ 2 * T
  complement_error : (h - d) ^ 2 / (N - m) ≤ 8 * T
  density_error :
    |(-d * Real.log (m / N) - (h - d) * Real.log (1 - m / N)) +
        d * Real.log p - p * n| ≤
      (relativeConstant T + 4 * relativeConstant T ^ 2 + 10) * Real.log n

set_option maxHeartbeats 1600000 in
theorem window_bounds {T p : ℝ} {n : ℕ} {N m h d : ℝ}
    (hT : 1 < T) (hlarge : LargeParameters T n p)
    (hcap : (n : ℝ) ^ 2 ≤ 4 * T * N)
    (hhlo : (n : ℝ) - 1 ≤ h) (hhhi : h ≤ n)
    (hmwindow : |m - p * N| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n))
    (hdwindow : |d - p * n| ≤ Real.sqrt (p * n) * Real.log (n : ℝ)) :
    RemovalBounds T n p N m h d := by
  rcases hlarge with ⟨hnsize, hlog, hp, hpsmall, hsparse, hscale⟩
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn64 : (64 : ℝ) ≤ n := by linarith
  have hN : 0 < N := by
    by_contra hc
    have hh := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4 * T) (le_of_not_gt hc)
    nlinarith [sq_pos_of_pos hn0]
  have hNbig : 16 * (n : ℝ) ≤ N := by
    have hh := mul_le_mul_of_nonneg_right hnsize hn0.le
    by_contra hc
    have hhpos := mul_pos hT0 (sub_pos.mpr (lt_of_not_ge hc))
    nlinarith
  have hh0 : 0 ≤ h := by linarith
  have hK : 0 < relativeConstant T := by dsimp [relativeConstant]; positivity
  have hu0 : 0 < p * (n : ℝ) := mul_pos hp hn0
  have hs0 : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr (mul_pos hp hn0)
  have hss : Real.sqrt (p * n) ^ 2 = p * n := Real.sq_sqrt (by positivity)
  have hL0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hsK : 2 * relativeConstant T ≤ Real.sqrt (p * n) := by
    nlinarith [mul_nonneg hK.le hL0]
  have hsL : 2 * Real.log (n : ℝ) ≤ Real.sqrt (p * n) := by
    nlinarith [mul_nonneg hK.le hL0]
  have hdev : |d - p * n| ≤ p * n / 2 := by
    have hh := mul_le_mul_of_nonneg_left hsL hs0.le
    nlinarith
  have hd0 : 0 ≤ d := by linarith [(abs_le.mp hdev).1]
  have hdu : d ≤ 2 * (p * n) := by linarith [(abs_le.mp hdev).2]
  have hdh : d ≤ h := by
    have hh := mul_le_mul_of_nonneg_right hpsmall hn0.le
    linarith
  have hcapT : T * (n : ℝ) ^ 2 ≤ relativeConstant T * N := by
    have hh := mul_le_mul_of_nonneg_left hcap hT0.le
    dsimp [relativeConstant]
    nlinarith
  have hdevm : |m - p * N| ≤ p * N / 2 := by
    have hh : T * (n : ℝ) ^ 2 * p ≤ relativeConstant T * (p * N) := by
      have ht := mul_le_mul_of_nonneg_right hcapT hp.le
      nlinarith
    have hh2 := mul_le_mul_of_nonneg_right hsK (mul_pos hp hN).le
    have hbound : T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ≤ p * N / 2 := by
      apply (div_le_iff₀ hs0).mpr
      nlinarith
    exact hmwindow.trans hbound
  have hmlo : p * N / 2 ≤ m := by linarith [(abs_le.mp hdevm).1]
  have hmhi : m ≤ 3 / 2 * p * N := by linarith [(abs_le.mp hdevm).2]
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hmlo
  have hmhalf : 2 * m ≤ N := by
    have hh := mul_le_mul_of_nonneg_right hpsmall hN.le
    linarith
  have hmN : m < N := by linarith
  have hcount : 2 * d ≤ m := by
    have hh := mul_le_mul_of_nonneg_left hNbig hp.le
    nlinarith
  have hroom : 2 * (h - d) ≤ N - m := by linarith
  have hcaperr : h ^ 2 / N ≤ 4 * T := by
    apply (div_le_iff₀ hN).mpr
    have hh := (sq_le_sq₀ hh0 hn0.le).mpr hhhi
    nlinarith
  have hmerr : d ^ 2 / m ≤ 2 * T := by
    apply (div_le_iff₀ hm0).mpr
    have hd2 := (sq_le_sq₀ hd0 (by positivity : 0 ≤ 2 * (p * n))).mpr hdu
    have h1 := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 4 * p ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hmlo (by positivity : 0 ≤ 32 * T * p)
    have h3 := mul_le_mul_of_nonneg_right hpsmall (by positivity : 0 ≤ 32 * T * m)
    nlinarith
  have hrerr : (h - d) ^ 2 / (N - m) ≤ 8 * T := by
    apply (div_le_iff₀ (sub_pos.mpr hmN)).mpr
    have hh := (sq_le_sq₀ (sub_nonneg.mpr hdh) hn0.le).mpr (show h - d ≤ n by linarith)
    have ht := mul_le_mul_of_nonneg_left hmhalf hT0.le
    nlinarith
  refine ⟨hN, hm0, hmN, hd0, hdh, by linarith, hcount, hroom, hcaperr, hmerr, hrerr, ?_⟩
  let t := (m - p * N) / (p * N)
  have hpN : 0 < p * N := mul_pos hp hN
  have hqt : m / N = p * (1 + t) := by
    dsimp [t]
    field_simp
    ring
  have ht : |t| ≤ 1 / 2 := by
    dsimp [t]
    rw [abs_div, abs_of_pos hpN, div_le_iff₀ hpN]
    linarith
  have hrelative : Real.sqrt (p * n) * |t| ≤ relativeConstant T := by
    dsimp [t]
    rw [abs_div, abs_of_pos hpN, ← mul_div_assoc, div_le_iff₀ hpN]
    have hh := (le_div_iff₀ hs0).mp hmwindow
    have hh2 := mul_le_mul_of_nonneg_right hcapT hp.le
    nlinarith
  have hqsmall : |m / N| ≤ 1 / 2 := by
    rw [abs_of_pos (div_pos hm0 hN), div_le_iff₀ hN]
    linarith
  have hcenter : |h * p - p * n| ≤ p := by
    apply abs_le.mpr
    have h1 := mul_le_mul_of_nonneg_right hhlo hp.le
    have h2 := mul_le_mul_of_nonneg_right hhhi hp.le
    constructor <;> nlinarith
  have he := density_error_bound hn0.le hp (by linarith : p ≤ 1) rfl
    hd0 hdh hhhi hdu hcenter hdwindow hK.le hlog ht hrelative hqt hqsmall hsparse
  apply he.trans
  have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * relativeConstant T ^ 2 + 10)
  nlinarith

end MajorityDynamics.Combinatorics.DegreeRatios
