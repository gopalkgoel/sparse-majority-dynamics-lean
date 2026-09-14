import MajorityDynamics.Binomial.ExpansionError

/-! # Final error envelope for the Gaussian comparison -/

noncomputable section
open Filter Topology
namespace MajorityDynamics.Binomial.Approximation

/-- Convert the integer-power estimates to the paper's real-power convention,
including constant monomials. -/
theorem gaussian_envelope (s l n : ℝ) (D d : ℕ)
    (hs : 1 ≤ s) (hl : 1 ≤ l) (hsn : s ≤ n) :
    (s ^ D / s) * l ^ (D + 3) ≤ s ^ ((D : ℝ) - 1) * l ^ (3 + D + d) ∧
    1 / n ≤ s ^ ((D : ℝ) - 1) * l ^ (3 + D + d) := by
  have hs0 : 0 < s := by linarith
  have hn0 : 0 < n := hs0.trans_le hsn
  have hpow : s ^ ((D : ℝ) - 1) = s ^ D / s := by
    rw [Real.rpow_sub hs0, Real.rpow_natCast, Real.rpow_one]
  rw [hpow]
  have hp : l ^ (D + 3) ≤ l ^ (3 + D + d) :=
    pow_le_pow_right₀ hl (by omega)
  have hbase : 0 ≤ s ^ D / s := by positivity
  constructor
  · exact mul_le_mul_of_nonneg_left hp hbase
  · have hinv := one_div_le_one_div_of_le hs0 hsn
    have hD : 1 ≤ s ^ D := one_le_pow₀ hs
    have hlD : 1 ≤ l ^ (3 + D + d) := one_le_pow₀ hl
    have hi : 1 / s ≤ s ^ D / s := div_le_div_of_nonneg_right hD hs0.le
    have hh := mul_le_mul_of_nonneg_left hlD hbase
    simp only [mul_one] at hh
    exact hinv.trans (hi.trans hh)

/-- A uniform threshold supplies all scalar window conditions before any trial
vector or tilt is chosen. -/
theorem eventually_gaussian_window (θ T : ℝ) (d : ℕ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      1 + 8 * T ^ 2 + 128 * d * T ≤ Real.log n ∧
      ∀ p : Probability, Density θ T n p →
        1024 * ((d : ℝ) + 1) * (T + 1) ^ 2 * (Real.log n) ^ 3 ≤ scale n p ∧
        (p : ℝ) ≤ 1 / 8 ∧ (p : ℝ) * scale n p ≤ 1 := by
  have hK : 0 < 1024 * ((d : ℝ) + 1) * (T + 1) ^ 2 := by positivity
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (1 + 8 * T ^ 2 + 128 * d * T))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog,
    density_scale_lower θ T _ hθhi hT hK,
    density_small_parameters θ T hθlo hT] with n hn hl hscale hsmall
  exact ⟨by omega, hl, fun p hp => ⟨hscale p hp, hsmall p hp⟩⟩

end MajorityDynamics.Binomial.Approximation
