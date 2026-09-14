import MajorityDynamics.Binomial.WindowPointEstimate
import MajorityDynamics.Binomial.DensityEstimates

/-! # The full two-tier point estimate of Appendix A.2 -/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Binomial.Approximation

private theorem window_bounds (n m : ℕ) (p : Probability) (T l : ℝ)
    (hn : 0 < (n : ℝ)) (hT : 0 < T) (hl : 1 ≤ l)
    (hp : (p : ℝ) ≤ 1 / 8) (hps : (p : ℝ) * scale n p ≤ 1)
    (hsT : 4 * T ≤ scale n p) (hsl : 1000 * l ^ 3 ≤ scale n p)
    (hm : |(m : ℝ) - n| < T * n / scale n p) :
    let μ := (p : ℝ) * n
    let L := scale n p * l
    0 < μ ∧ μ < m ∧ 1 ≤ L ∧ L ≤ ((m : ℝ) - μ) / 2 ∧ L ≤ μ / 2 ∧
    4 * L ^ 2 / ((m : ℝ) - μ) ≤ 1 ∧
    2 * L * gaussianStepError m μ L ≤ 1 ∧
    8 * L ^ 2 / ((m : ℝ) - μ) ≤ 32 * (p : ℝ) * l ^ 2 ∧
    4 * L * gaussianStepError m μ L ≤ 42 * l ^ 3 / scale n p := by
  have hp0 := p.property.1
  let s := scale n p
  let μ := (p : ℝ) * n
  let L := s * l
  have hμ : 0 < μ := mul_pos p.property.1 hn
  have hs : 0 < s := Real.sqrt_pos.mpr hμ
  have hsq : s ^ 2 = μ := Real.sq_sqrt hμ.le
  have hl0 : 0 ≤ l := by linarith
  have hl2 : l ^ 2 ≤ l ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hl (sq_nonneg l)]
  have hl3 : l ≤ l ^ 3 := by nlinarith [sq_nonneg (l - 1)]
  have hl31 : 1 ≤ l ^ 3 := le_trans hl hl3
  have hs1 : 1 ≤ s := by change 1000 * l ^ 3 ≤ s at hsl; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; nlinarith
  have htrial : T * n / s ≤ (n : ℝ) / 4 := by
    apply (div_le_iff₀ hs).mpr
    have h := mul_le_mul_of_nonneg_left hsT hn.le
    change 4 * T ≤ s at hsT
    nlinarith
  have hmN : (n : ℝ) / 2 ≤ m := by
    have hb := (abs_lt.mp hm).1
    change T * n / s ≤ (n : ℝ) / 4 at htrial
    change -(T * n / s) < (m : ℝ) - n at hb
    linarith
  have hμN : μ ≤ (n : ℝ) / 8 := by
    have := mul_le_mul_of_nonneg_right hp hn.le
    dsimp [μ]
    linarith
  have hmμ : μ < m := by linarith
  have hd : 0 < (m : ℝ) - μ := sub_pos.mpr hmμ
  have hn4 : (n : ℝ) ≤ 4 * ((m : ℝ) - μ) := by linarith
  have hμd : μ ≤ (m : ℝ) - μ := by linarith
  have hsucc : L ≤ μ / 2 := by
    have h2l : 2 * l ≤ s := by change 1000 * l ^ 3 ≤ s at hsl; linarith
    have h := mul_le_mul_of_nonneg_left h2l hs.le
    dsimp [L]
    nlinarith [hsq]
  have hcomp : L ≤ ((m : ℝ) - μ) / 2 := hsucc.trans (by linarith)
  have hRsmall : l ^ 3 / s ≤ 1 / 1000 := by
    apply (div_le_iff₀ hs).mpr
    change 1000 * l ^ 3 ≤ s at hsl
    linarith
  have hpR : (p : ℝ) * l ^ 2 ≤ l ^ 3 / s := by
    apply (le_div_iff₀ hs).mpr
    have h := mul_le_mul_of_nonneg_right hps (sq_nonneg l)
    change (p : ℝ) * s ≤ 1 at hps
    nlinarith
  have hlR : l / s ≤ l ^ 3 / s := (div_le_div_iff_of_pos_right hs).mpr hl3
  have herr1 : 8 * L ^ 2 / ((m : ℝ) - μ) ≤ 32 * (p : ℝ) * l ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    calc
      _ = (8 * (p : ℝ) * l ^ 2) * n := by dsimp [L]; rw [mul_pow, hsq]; dsimp [μ]; ring
      _ ≤ (8 * (p : ℝ) * l ^ 2) * (4 * ((m : ℝ) - μ)) :=
        mul_le_mul_of_nonneg_left hn4 (by positivity)
      _ = _ := by ring
  have hid : 4 * L * gaussianStepError m μ L =
      8 * L ^ 2 / ((m : ℝ) - μ) + 8 * l ^ 3 / s + 2 * l / s := by
    dsimp [gaussianStepError, L]
    rw [← hsq]
    field_simp
    ring
  have herr2 : 4 * L * gaussianStepError m μ L ≤ 42 * l ^ 3 / s := by
    rw [hid]
    simp only [div_eq_mul_inv] at herr1 hpR hlR ⊢
    nlinarith only [herr1, hpR, hlR]
  have hsmall1 : 4 * L ^ 2 / ((m : ℝ) - μ) ≤ 1 := by
    simp only [div_eq_mul_inv] at herr1 hpR hRsmall ⊢
    nlinarith only [herr1, hpR, hRsmall]
  have hsmall2 : 2 * L * gaussianStepError m μ L ≤ 1 := by
    simp only [div_eq_mul_inv] at herr2 hRsmall
    nlinarith only [herr2, hRsmall]
  exact ⟨hμ, hmμ, hL1, hcomp, hsucc, hsmall1, hsmall2, herr1, herr2⟩

/-- The exact A.2 point-estimate target. The proof in fact works for every
success probability `q ∈ (0,1)` once the trial/center/window conditions hold. -/
theorem point_estimate : PointEstimateTheorem := by
  intro θ T hθ₀ hθ₁ hT
  have hT0 : 0 < T := by linarith
  let K := max (4 * T) 1000
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1000) (le_max_right _ _)
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlarge : ∀ᶠ n : ℕ in atTop, ∀ p : Probability, Density θ T n p →
      0 < (n : ℝ) ∧ 1 ≤ Real.log n ∧ (p : ℝ) ≤ 1 / 8 ∧
      (p : ℝ) * scale n p ≤ 1 ∧ 4 * T ≤ scale n p ∧
      1000 * (Real.log n) ^ 3 ≤ scale n p := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1,
      density_scale_lower θ T K hθ₁ hT0 hK,
      density_small_parameters θ T hθ₀ hT0] with n hn1 hlog hscale hsmall
    intro p hp
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hl3 : (1 : ℝ) ≤ (Real.log n) ^ 3 := one_le_pow₀ hlog
    have hsk := hscale p hp
    have hk1 := le_max_left (4 * T) 1000
    have hk2 := le_max_right (4 * T) 1000
    have hsT : 4 * T ≤ scale n p := by
      have h := mul_le_mul_of_nonneg_left hl3 hK.le
      dsimp [K] at h hsk
      linarith
    have hslog : 1000 * (Real.log n) ^ 3 ≤ scale n p := by
      have h := mul_le_mul_of_nonneg_right hk2 (show 0 ≤ (Real.log n) ^ 3 by positivity)
      exact h.trans hsk
    exact ⟨hn0, hlog, (hsmall p hp).1, (hsmall p hp).2, hsT, hslog⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hlarge
  refine ⟨42, by norm_num, n₀, ?_⟩
  intro n hn0 p hp m q hm _
  obtain ⟨hnpos, hlog, hp8, hps, hsT, hsl⟩ := hn₀ n hn0 p hp
  obtain ⟨hμ, hmμ, hL, hcomp, hsucc, hsmall1, hsmall2, herr1, herr2⟩ :=
    window_bounds n m p T (Real.log n) hnpos hT0 hlog hp8 hps hsT hsl hm
  obtain ⟨N₁, hN₁, hfirst⟩ := first_window_estimate m ((p : ℝ) * n)
    (scale n p * Real.log n) q hμ hmμ hL hcomp hsmall1
  obtain ⟨N₂, hN₂, hsecond⟩ := gaussian_window_estimate m ((p : ℝ) * n)
    (scale n p * Real.log n) q hμ hmμ hL hcomp hsucc hsmall2
  refine ⟨N₁, N₂, hN₁, hN₂, ?_⟩
  intro k hk
  have hsq : scale n p ^ 2 = (p : ℝ) * n := Real.sq_sqrt hμ.le
  have hslope : windowSlope m ((p : ℝ) * n) q = pointSlope n m p q := rfl
  have hF := (hfirst k hk).trans (mul_le_mul_of_nonneg_right herr1 (abs_nonneg _))
  have hG := (hsecond k hk).trans (mul_le_mul_of_nonneg_right herr2 (abs_nonneg _))
  dsimp only
  constructor
  · have hc : 32 * (p : ℝ) * (Real.log n) ^ 2 ≤ 42 * (p : ℝ) * (Real.log n) ^ 2 := by
      have := mul_nonneg p.property.1.le (sq_nonneg (Real.log (n : ℝ)))
      nlinarith
    have h := hF.trans (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    simpa only [firstShape, hslope, mul_assoc] using h
  · have he : scale n p * Real.log (pointSlope n m p q) * scale n p =
        ((p : ℝ) * n) * Real.log (pointSlope n m p q) := by
      calc
        _ = scale n p ^ 2 * Real.log (pointSlope n m p q) := by ring
        _ = _ := by rw [hsq]
    simpa only [hslope, gaussianShape, he] using hG

end MajorityDynamics.Binomial.Approximation
