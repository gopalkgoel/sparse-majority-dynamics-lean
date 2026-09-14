import MajorityDynamics.Binomial.SparseRange

/-! Any fixed logarithmic loss is affordable on the sparse range. -/
noncomputable section
open Filter Topology
namespace MajorityDynamics.Binomial.Approximation

theorem sparseRange_scale_log_power (θ T K : ℝ) (k : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      K * (Real.log N) ^ k ≤ scale N p := by
  have hN := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := ((isLittleO_log_rpow_rpow_atTop (2 * k : ℕ)
    (by linarith : 0 < 1 - θ)).comp_tendsto hN).bound
      (show 0 < (T * K ^ 2)⁻¹ by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with N hN1 hbound
  intro p hp
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN1
  have hμ : 0 ≤ (p : ℝ) * N := mul_nonneg p.property.1.le hN0.le
  have hpow : (N : ℝ) ^ (1 - θ) = (N : ℝ) ^ (-θ) * N := by
    rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hN0.ne']
  have hlogpos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hbound' : (Real.log N) ^ (2 * k) ≤
      (T * K ^ 2)⁻¹ * (N : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, norm_pow,
      Real.norm_of_nonneg hlogpos,
      Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _)] using hbound
  have hd := mul_lt_mul_of_pos_right hp.1 hN0
  rw [mul_assoc, ← hpow] at hd
  have hsq : (K * (Real.log N) ^ k) ^ 2 ≤ (p : ℝ) * N := by
    have hh := mul_le_mul_of_nonneg_left hbound' (sq_nonneg K)
    have heq : K ^ 2 * ((T * K ^ 2)⁻¹ * (N : ℝ) ^ (1 - θ)) =
        T⁻¹ * (N : ℝ) ^ (1 - θ) := by field_simp
    rw [heq, show 2 * k = k * 2 by omega, pow_mul] at hh
    nlinarith
  exact (Real.le_sqrt (by positivity) hμ).mpr hsq

/-- A polynomial gain at an inverse-logarithmic threshold dominates the
normalized cleanup target. The exponent d may be the entire row dimension. -/
theorem sparseRange_polynomial_gain_budget (θ T c : ℝ) (M d : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      ∀ u : ℝ, 0 ≤ u → 1 ≤ u * (Real.log N) ^ M →
      Real.log N / scale N p ≤ c * u ^ d := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    sparseRange_scale_log_power θ T c⁻¹ (M * d + 1) hθ hT (inv_pos.mpr hc)]
    with N hN hs
  intro p hp u hu hthreshold
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hspos : 0 < scale N p := by
    unfold scale
    apply Real.sqrt_pos.mpr
    exact mul_pos p.property.1 (by exact_mod_cast (show 0 < N by omega))
  have hscale := hs p hp
  have hpower : 1 ≤ u ^ d * (Real.log N) ^ (M * d) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hthreshold d
    simpa only [one_pow, mul_pow, ← pow_mul] using h
  apply (div_le_iff₀ hspos).mpr
  have h1 := mul_le_mul_of_nonneg_right hpower hlog.le
  have h2 := mul_le_mul_of_nonneg_left hscale (mul_nonneg hc.le (pow_nonneg hu d))
  have hid : c * u ^ d * (c⁻¹ * (Real.log N) ^ (M * d + 1)) =
      (u ^ d * (Real.log N) ^ (M * d)) * Real.log N := by
    rw [pow_succ]
    field_simp
  rw [hid] at h2
  simpa only [one_mul] using h1.trans h2

end MajorityDynamics.Binomial.Approximation
