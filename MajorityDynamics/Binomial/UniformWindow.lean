import MajorityDynamics.Binomial.WindowBounds

/-! # Uniform admissibility of the A.2 logarithmic window -/

noncomputable section
open Filter Topology
namespace MajorityDynamics.Binomial.Approximation

/-- Sufficient scalar conditions for every allowed trial vector and tilt.
The logarithmic threshold depends only on fixed dimension and size constants. -/
theorem logarithmic_window_conditions (d T n p s l B : ℝ)
    (hd : 1 ≤ d) (hT : 1 ≤ T) (_hn : 0 < n) (hp : 0 < p) (hp1 : p ≤ 1)
    (hs : 0 < s) (hscale : s ^ 2 = p * n)
    (hl : 1 + 8 * T ^ 2 + 128 * d * T ≤ l)
    (hls : l ^ 3 ≤ s) (hps : p * s ≤ 1)
    (_hB : 0 ≤ B) (hBsmall : B ≤ T / (s * l ^ 2)) :
    4 * T ^ 2 ≤ s ∧ p ≤ 1 / (8 * T ^ 2) ∧
    1 ≤ s * l ∧ s * l ≤ n / (8 * T) ∧
    6 * T ^ 2 ≤ l ∧ l ≤ s ∧
    d * B * (s * l) ≤ 1 / 4 ∧ 32 * d * T * p * l ^ 2 ≤ 1 / 4 ∧ B ≤ 1 := by
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have hl1 : 1 ≤ l := by nlinarith
  have hl0 : 0 < l := by linarith
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have h8 : 8 * T ^ 2 ≤ l := by nlinarith
  have h128 : 128 * d * T ≤ l := by nlinarith
  have hl2 : l ≤ l ^ 2 := by nlinarith
  have hl3 : l ^ 2 ≤ l ^ 3 := by nlinarith [mul_nonneg (sq_nonneg l) (show 0 ≤ l - 1 by linarith)]
  have hsl : l ≤ s := hl2.trans (hl3.trans hls)
  have hs1 : 1 ≤ s := hl1.trans hsl
  have hlarge : 4 * T ^ 2 ≤ s := by nlinarith
  have hp8 : p ≤ 1 / (8 * T ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (h8.trans hsl) hp.le]
  have hL1 : 1 ≤ s * l := by nlinarith
  have hLupper : s * l ≤ n / (8 * T) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h8T : 8 * T ≤ l := by nlinarith
    have hsl2 : l ^ 2 ≤ s := hl3.trans hls
    have hpl : p * (8 * T * l) ≤ s := by
      have h := mul_le_mul_of_nonneg_right h8T hl0.le
      have h' := mul_le_mul_of_nonneg_left h hp.le
      nlinarith [mul_le_mul_of_nonneg_right hp1 (sq_nonneg l)]
    have h := mul_le_mul_of_nonneg_left hpl hs.le
    nlinarith [hscale]
  have hb : d * B * (s * l) ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < s * l ^ 2)).mp hBsmall
    have h' := mul_le_mul_of_nonneg_left h hd0.le
    have h4 : 4 * d * T ≤ l := by nlinarith
    have hh : (d * B * (s * l)) * l ≤ d * T := by nlinarith only [h']
    nlinarith only [hh, h4, hl0]
  have hδ : 32 * d * T * p * l ^ 2 ≤ 1 / 4 := by
    have hpl3 : p * l ^ 3 ≤ 1 := (mul_le_mul_of_nonneg_left hls hp.le).trans hps
    have hh := mul_le_mul_of_nonneg_right h128 (mul_nonneg hp.le (sq_nonneg l))
    nlinarith only [hpl3, hh]
  have hB1 : B ≤ 1 := by
    have hden : T ≤ s * l ^ 2 := by
      have hTs : T ≤ s := by nlinarith
      nlinarith [mul_nonneg hs.le (show 0 ≤ l ^ 2 - 1 by nlinarith)]
    exact hBsmall.trans ((div_le_one (by positivity : 0 < s * l ^ 2)).mpr hden)
  exact ⟨hlarge, hp8, hL1, hLupper, by nlinarith, hsl, hb, hδ, hB1⟩

theorem eventually_logarithmic_window (θ T : ℝ) (d : ℕ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      1 + 8 * T ^ 2 + 128 * d * T ≤ Real.log n ∧
      ∀ p : Probability, Density θ T n p →
        (Real.log n) ^ 3 ≤ scale n p ∧ (p : ℝ) * scale n p ≤ 1 := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (1 + 8 * T ^ 2 + 128 * d * T))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog,
    density_scale_lower θ T 1 hθhi hT zero_lt_one,
    density_small_parameters θ T hθlo hT] with n hn hl hscale hsmall
  refine ⟨by omega, hl, ?_⟩
  intro p hp
  exact ⟨by simpa using hscale p hp, (hsmall p hp).2⟩

end MajorityDynamics.Binomial.Approximation
