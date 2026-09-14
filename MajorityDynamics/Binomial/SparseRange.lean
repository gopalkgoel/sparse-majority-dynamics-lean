import MajorityDynamics.Binomial.DensityEstimates

/-!
# A one-sided density range for uniform estimates

`SparseRange θ T N p` keeps the lower bound from the main theorem but permits
`p` to vary all the way up to the square-root scale.  The two ends of the
range play different roles: the lower bound makes `sqrt (pN)` dominate every
fixed logarithmic power, while the upper bound makes `p * sqrt (pN)` vanish.
-/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Binomial.Approximation

def SparseRange (θ T : ℝ) (N : ℕ) (p : Probability) : Prop :=
  T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) ∧
    (p : ℝ) < T * (N : ℝ) ^ (-(1 / 2 : ℝ))

/-- The lower endpoint alone makes the binomial standard deviation dominate
any fixed multiple of `log N ^ 3`. -/
theorem sparseRange_scale_lower (θ T K : ℝ) (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      K * (Real.log N) ^ 3 ≤ scale N p := by
  have hN := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := ((isLittleO_log_rpow_rpow_atTop 6 (by linarith : 0 < 1 - θ)).comp_tendsto
    hN).bound (show 0 < (T * K ^ 2)⁻¹ by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with N hN1 hbound
  intro p hp
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN1
  have hμ : 0 ≤ (p : ℝ) * N := mul_nonneg p.property.1.le hN0.le
  have hpow : (N : ℝ) ^ (1 - θ) = (N : ℝ) ^ (-θ) * N := by
    rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hN0.ne']
  have hlogpos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hbound' : (Real.log N) ^ 6 ≤
      (T * K ^ 2)⁻¹ * (N : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_ofNat, norm_pow,
      Real.norm_of_nonneg hlogpos,
      Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _)] using hbound
  have hd := mul_lt_mul_of_pos_right hp.1 hN0
  rw [mul_assoc, ← hpow] at hd
  have hsq : (K * (Real.log N) ^ 3) ^ 2 ≤ (p : ℝ) * N := by
    have hh := mul_le_mul_of_nonneg_left hbound' (sq_nonneg K)
    have heq : K ^ 2 * ((T * K ^ 2)⁻¹ * (N : ℝ) ^ (1 - θ)) =
        T⁻¹ * (N : ℝ) ^ (1 - θ) := by field_simp
    rw [heq] at hh
    nlinarith
  exact (Real.le_sqrt (by positivity) hμ).mpr hsq

/-- The square-root upper endpoint is sparse enough for the A.2 parameter
`p * sqrt (pN)` to tend uniformly to zero. -/
theorem sparseRange_small_parameters (θ T : ℝ) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      (p : ℝ) ≤ 1 / 8 ∧ (p : ℝ) * scale N p ≤ 1 := by
  have hN := tendsto_natCast_atTop_atTop (R := ℝ)
  have hup : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hN).const_mul T
  have hmid : Tendsto
      (fun N : ℕ => T * Real.sqrt T * (N : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hN).const_mul
        (T * Real.sqrt T)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hup.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    hmid.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN1 hu hm
  intro p hp
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN1
  have hupper : (p : ℝ) ≤ T * (N : ℝ) ^ (-(1 / 2 : ℝ)) := hp.2.le
  refine ⟨hupper.trans hu.le, ?_⟩
  have hpN : (p : ℝ) * N ≤ T * (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (p : ℝ) * N ≤ (T * (N : ℝ) ^ (-(1 / 2 : ℝ))) * N :=
        mul_le_mul_of_nonneg_right hupper hN0.le
      _ = T * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * N) := by ring
      _ = T * (N : ℝ) ^ (-(1 / 2 : ℝ) + 1) := by
        rw [Real.rpow_add_one hN0.ne']
      _ = T * (N : ℝ) ^ (1 / 2 : ℝ) := by
        congr 1
        ring
  have hscale : scale N p ≤ Real.sqrt T * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have hsqrt := Real.sqrt_le_sqrt hpN
    unfold scale
    rw [Real.sqrt_mul hT.le] at hsqrt
    refine hsqrt.trans_eq ?_
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  calc
    (p : ℝ) * scale N p ≤
        (T * (N : ℝ) ^ (-(1 / 2 : ℝ))) *
          (Real.sqrt T * (N : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul hupper hscale (Real.sqrt_nonneg _) (by positivity)
    _ = T * Real.sqrt T * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ 1 := hm.le

/-- The lower endpoint also absorbs the final `1/N` tail term into the `p`
part of the finite-tilt error. -/
theorem sparseRange_inverse_size {θ T : ℝ} {N : ℕ} {p : Probability}
    (hθ : θ < 1) (hT : 0 < T) (hN : 1 ≤ N) (hp : SparseRange θ T N p) :
    1 / (N : ℝ) ≤ T * (p : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-θ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_neg_one] at hpow
  have hh := mul_le_mul_of_nonneg_left hp.1.le hT.le
  simp only [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at hh
  simpa only [one_div] using hpow.trans hh

/-- All scalar hypotheses used by both A.2 endpoints hold uniformly on the
entire one-sided sparse range. -/
theorem eventually_sparseRange_window (θ T : ℝ) (d : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧
      1 + 8 * T ^ 2 + 128 * d * T ≤ Real.log N ∧
      ∀ p : Probability, SparseRange θ T N p →
        1024 * ((d : ℝ) + 1) * (T + 1) ^ 2 * (Real.log N) ^ 3 ≤ scale N p ∧
        (p : ℝ) ≤ 1 / 8 ∧ (p : ℝ) * scale N p ≤ 1 ∧
        1 / (N : ℝ) ≤ T * (p : ℝ) := by
  have hK : 0 < 1024 * ((d : ℝ) + 1) * (T + 1) ^ 2 := by positivity
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (1 + 8 * T ^ 2 + 128 * d * T))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog,
    sparseRange_scale_lower θ T _ hθ hT hK,
    sparseRange_small_parameters θ T hT] with N hN hlog hscale hsmall
  refine ⟨by omega, hlog, ?_⟩
  intro p hp
  exact ⟨hscale p hp, (hsmall p hp).1, (hsmall p hp).2,
    sparseRange_inverse_size hθ hT hN hp⟩

end MajorityDynamics.Binomial.Approximation
