import MajorityDynamics.Binomial.DensityEstimates

/-! Scalar geometry behind the E.3 diagonal trial correction and normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology

namespace MajorityDynamics.Idealized.RowLimits
open Binomial Binomial.Approximation

/-- The A.2 tilt parameter expressed in the macroscopic E.3 coordinates. -/
def rowAlpha (N : ℕ) (m σ ν : ℝ) : ℝ := σ / ν * Real.sqrt (m / N)

theorem rowAlpha_exponent (N : ℕ) (hN : 0 < N) (p : Probability)
    (m σ ν : ℝ) (hm : 0 < m) :
    rowAlpha N m σ ν / Real.sqrt ((p : ℝ) * m) =
      σ / (ν * scale N p) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp := p.property.1
  have hsn : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have hsp : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [rowAlpha, scale, Real.sqrt_div hm.le, Real.sqrt_mul hp.le]
  field_simp

theorem rowAlpha_logit (N : ℕ) (hN : 0 < N) (p : Probability)
    (m : ℕ) (hm : 0 < m) (σ ν : ℝ) :
    logistic (logOdds p + rowAlpha N m σ ν / Real.sqrt ((p : ℝ) * m)) =
      logitTilt N p σ ν := by
  rw [rowAlpha_exponent N hN p m σ ν (by exact_mod_cast hm)]
  rfl

theorem normalized_variance_error (N η ν δ e : ℝ) (hN : 0 < N)
    (hδ : |δ| ≤ 1) (hη : |η - N * ν| ≤ N * e) :
    |(η - δ) / N - ν| ≤ e + 1 / N := by
  have hid : (η - δ) / N - ν = ((η - N * ν) - δ) / N := by field_simp; ring
  rw [hid, abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  have hh := (abs_sub (η - N * ν) δ).trans (add_le_add hη hδ)
  calc
    |η - N * ν - δ| ≤ N * e + 1 := hh
    _ = (e + 1 / N) * N := by field_simp

theorem normalized_mean_error (N η σ ν δ e R : ℝ) (hN : 0 < N)
    (hν : 0 < ν) (hδ : |δ| ≤ 1) (hη : |η - N * ν| ≤ N * e)
    (hσ : |σ| ≤ R) :
    |σ * (η - δ) / (N * ν) - σ| ≤ R / ν * (e + 1 / N) := by
  have hv := normalized_variance_error N η ν δ e hN hδ hη
  have hid : σ * (η - δ) / (N * ν) - σ =
      σ / ν * ((η - δ) / N - ν) := by field_simp
  rw [hid, abs_mul, abs_div, abs_of_pos hν]
  exact mul_le_mul (div_le_div_of_nonneg_right hσ hν.le) hv
    (abs_nonneg _) (div_nonneg ((abs_nonneg σ).trans hσ) hν.le)

theorem corrected_trial_interval (N η ν δ e : ℝ) (hN : 0 < N)
    (hν : 0 < ν) (hδ : |δ| ≤ 1) (hη : |η - N * ν| ≤ N * e)
    (he : e + 1 / N < ν / 2) :
    N * ν / 2 < η - δ ∧ η - δ < 2 * N * ν := by
  have hv := lt_of_le_of_lt (normalized_variance_error N η ν δ e hN hδ hη) he
  have hh := abs_lt.mp hv
  constructor
  · have hb : ν / 2 < (η - δ) / N := by linarith
    have := (lt_div_iff₀ hN).mp hb
    nlinarith
  · have hb : (η - δ) / N < 2 * ν := by linarith
    have := (div_lt_iff₀ hN).mp hb
    nlinarith

/-- Uniform logarithmic domination for every fixed power, with the density
    quantified after the common eventual threshold. -/
theorem density_scale_lower_power (θ T K : ℝ) (L : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Probability, Density θ T n p →
      K * (Real.log n) ^ L ≤ scale n p := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := ((isLittleO_log_rpow_rpow_atTop ((2 * L : ℕ) : ℝ)
    (by linarith : 0 < 1 - θ)).comp_tendsto hn).bound
      (show 0 < (T * K ^ 2)⁻¹ by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with n hn1 hbound
  intro p hp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hμ : 0 ≤ (p : ℝ) * n := mul_nonneg p.property.1.le hn0.le
  have hpow : (n : ℝ) ^ (1 - θ) = (n : ℝ) ^ (-θ) * n := by
    rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hn0.ne']
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hbound' : (Real.log n) ^ (2 * L) ≤
      (T * K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, norm_pow,
      Real.norm_of_nonneg hlogpos,
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hbound
  have hd := mul_lt_mul_of_pos_right hp.1 hn0
  rw [mul_assoc, ← hpow] at hd
  have hsq : (K * (Real.log n) ^ L) ^ 2 ≤ (p : ℝ) * n := by
    have hh := mul_le_mul_of_nonneg_left hbound' (sq_nonneg K)
    have heq : K ^ 2 * ((T * K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ)) =
        T⁻¹ * (n : ℝ) ^ (1 - θ) := by field_simp
    rw [heq, show 2 * L = L * 2 by omega, pow_mul] at hh
    nlinarith
  exact (Real.le_sqrt (by positivity) hμ).mpr hsq

/-- The size-error radius tends uniformly to zero in the permitted density range. -/
theorem eventually_size_error_small (θ T ε : ℝ) (L : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ p : Probability, Density θ T n p →
      (Real.log n) ^ L / scale n p + 1 / n < ε := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
    exact tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    density_scale_lower_power θ T (4 / ε) L hθ hT (by positivity),
    hinv.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))]
    with n hn hscale hi
  refine ⟨by omega, ?_⟩
  intro p hp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < scale n p := Real.sqrt_pos.mpr (mul_pos p.property.1 hn0)
  have hb : (Real.log n) ^ L / scale n p ≤ ε / 4 := by
    apply (div_le_iff₀ hs).mpr
    have hh := hscale p hp
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ ε / 4 by positivity)
    have hid : ε / 4 * (4 / ε * (Real.log n) ^ L) = (Real.log n) ^ L := by field_simp
    rwa [hid] at hh'
  linarith

/-- Exact real conversion of the paper's integer diagonal correction. -/
theorem corrected_trial_cast (η : ℤ) (δ : ℕ) (h : (δ : ℤ) ≤ η) :
    (((η - δ).toNat : ℕ) : ℝ) = (η : ℝ) - δ := by
  have hc := Int.toNat_of_nonneg (sub_nonneg.mpr h)
  have hh := congrArg (fun z : ℤ => (z : ℝ)) hc
  simpa using hh

/-- The bounded A.2 tilts stay in a fixed compact interval. -/
theorem rowAlpha_bound (N : ℕ) (hN : 0 < N) (m σ ν R : ℝ)
    (_hm : 0 ≤ m) (hν : 0 < ν) (hσ : |σ| ≤ R)
    (hupper : m ≤ 2 * N * ν) :
    |rowAlpha N m σ ν| ≤ R / ν * Real.sqrt (2 * ν) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (m / N) ≤ Real.sqrt (2 * ν) := by
    apply Real.sqrt_le_sqrt
    apply (div_le_iff₀ hn).mpr
    nlinarith only [hupper]
  simp only [rowAlpha, abs_mul, abs_div, abs_of_pos hν,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (div_le_div_of_nonneg_right hσ hν.le) hs (by positivity)
    (div_nonneg ((abs_nonneg σ).trans hσ) hν.le)

/-- Gaussian mean normalization is exact, before any limiting estimate. -/
theorem rowAlpha_normalized_mean (N : ℕ) (hN : 0 < N) (p : Probability)
    (m σ ν : ℝ) (hm : 0 < m) :
    Real.sqrt ((p : ℝ) * m) * rowAlpha N m σ ν / scale N p =
      σ * m / (N * ν) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp := p.property.1
  have hsn : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hsp : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hmn := Real.sq_sqrt hm.le
  have hnn := Real.sq_sqrt hn.le
  simp only [rowAlpha, scale, Real.sqrt_div hm.le, Real.sqrt_mul hp.le]
  field_simp
  rw [hmn, hnn]
  ring

/-- All elementary normalization errors fit the stated logarithmic rate. -/
theorem elementary_errors_le_rate (N L : ℕ) (p : Probability)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    1 / (N : ℝ) ≤ Real.log N ^ L / scale N p ∧
    (p : ℝ) / scale N p ≤ Real.log N ^ L / scale N p := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < scale N p := Real.sqrt_pos.mpr (mul_pos p.property.1 hn)
  have hscale : scale N p ≤ N := by
    apply (Real.sqrt_le_left hn.le).mpr
    have hh := mul_le_mul_of_nonneg_right p.property.2.le hn.le
    nlinarith
  have hpow : 1 ≤ Real.log N ^ L := one_le_pow₀ hlog
  constructor
  · calc
      1 / (N : ℝ) ≤ 1 / scale N p := one_div_le_one_div_of_le hs hscale
      _ ≤ Real.log N ^ L / scale N p := div_le_div_of_nonneg_right hpow hs.le
  · exact div_le_div_of_nonneg_right (p.property.2.le.trans hpow) hs.le

 theorem logarithmic_rate_mono (N L L' : ℕ) (p : Probability)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hL : L ≤ L') :
    Real.log N ^ L / scale N p ≤ Real.log N ^ L' / scale N p :=
  div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog hL) (Real.sqrt_nonneg _)

end MajorityDynamics.Idealized.RowLimits
