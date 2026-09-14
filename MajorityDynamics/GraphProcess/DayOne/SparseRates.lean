import MajorityDynamics.GraphProcess.FaithfulStep.SparseRates

noncomputable section
open Filter Topology
namespace MajorityDynamics.GraphProcess.DayOne
open Idealized.LinearResponse Binomial.Approximation

/-- Day-one random fluctuations and deterministic centering errors fit the
paper's coefficient-one faithful bounds uniformly throughout the density window. -/
theorem eventually_faithful_errors_sparse {θ T K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      2 ≤ Real.sqrt (N : ℝ) * (N : ℝ)^(-((1-θ)/4)) ∧
      2 * (N : ℝ) * Real.sqrt (p : ℝ) * Real.log (N : ℝ) + K * N * p ≤
        betaScale N p 0 * (N : ℝ)^(-((1-θ)/4)) * (N : ℝ)^2 * p := by
  have hT0 : 0 < T := by linarith
  have hgap : (1-θ)/4 < (1:ℝ)/2 := by linarith
  have hgap' : (1-θ)/4 < (1-θ)/2 := by linarith
  filter_upwards [eventually_basic_sparse θ T hθlo hθhi hT,
    eventually_poly_log_le 2 (1/2) ((1-θ)/4) 0 (by norm_num) hgap,
    eventually_poly_log_le (2*K) (1/2) ((1-θ)/4) 0 (by positivity) hgap,
    eventually_poly_log_le (4*Real.sqrt T) ((1-θ)/2) ((1-θ)/4) 1
      (by positivity) hgap'] with N hb hsize hcenter hnoise
  intro p hp
  have hN : (0 : ℝ) < N := by exact_mod_cast hb.1
  have hp0 : 0 < (p : ℝ) := p.property.1
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hsx : 0 < Real.sqrt ((p : ℝ)*N) := Real.sqrt_pos.mpr (mul_pos hp0 hN)
  have hid : (N : ℝ)^(-(1:ℝ)/2) = (Real.sqrt (N : ℝ))⁻¹ := by
    rw [show -(1:ℝ)/2 = -(1/2) by ring, Real.rpow_neg hN.le, Real.sqrt_eq_rpow]
  simp only [pow_zero, mul_one] at hsize hcenter
  rw [show (-(1 / 2 : ℝ)) = -1/2 by ring, hid] at hsize hcenter
  have hsize' : 2 ≤ Real.sqrt (N : ℝ) * (N : ℝ)^(-((1-θ)/4)) := by
    have h := mul_le_mul_of_nonneg_left hsize hsN.le
    field_simp at h
    nlinarith only [h]
  refine ⟨hsize', ?_⟩
  have hlo := sqrt_pN_lower_sparse hb.1 hT0 hp
  have hinv : (Real.sqrt ((p : ℝ)*N))⁻¹ ≤
      Real.sqrt T * (N : ℝ)^(-((1-θ)/2)) := by
    rw [inv_eq_one_div, div_le_iff₀ hsx]
    have hh := mul_le_mul_of_nonneg_left hlo
      (show 0 ≤ Real.sqrt T * (N : ℝ)^(-((1-θ)/2)) by positivity)
    have hid' : Real.sqrt T * (N : ℝ)^(-((1-θ)/2)) *
        ((Real.sqrt T)⁻¹ * (N : ℝ)^((1-θ)/2)) = 1 := by
      rw [Real.rpow_neg hN.le]
      field_simp
    rw [hid'] at hh
    exact hh
  have hn : 4 * Real.log (N : ℝ) / Real.sqrt ((p : ℝ)*N) ≤
      (N : ℝ)^(-((1-θ)/4)) := by
    calc
      _ ≤ 4 * Real.log (N : ℝ) * (Real.sqrt T * (N : ℝ)^(-((1-θ)/2))) := by
        exact mul_le_mul_of_nonneg_left hinv (by nlinarith [hb.2.1])
      _ ≤ _ := by simpa only [pow_one, mul_assoc, mul_comm, mul_left_comm] using hnoise
  have hc : 2*K / Real.sqrt (N : ℝ) ≤ (N : ℝ)^(-((1-θ)/4)) := by
    simpa only [div_eq_mul_inv] using hcenter
  have htotal : 2 * Real.log (N : ℝ) / Real.sqrt ((p : ℝ)*N) +
      K / Real.sqrt (N : ℝ) ≤ (N : ℝ)^(-((1-θ)/4)) := by
    simp only [div_eq_mul_inv] at hn hc ⊢
    linarith
  have hmul := mul_le_mul_of_nonneg_right htotal
    (show 0 ≤ (N : ℝ)^2 * (p : ℝ) / Real.sqrt (N : ℝ) by positivity)
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  have hsqN := Real.sq_sqrt hN.le
  have hsqP := Real.sq_sqrt hp0.le
  rw [Real.sqrt_mul hp0.le] at hmul
  simp only [betaScale, pow_zero]
  field_simp at hmul ⊢
  have hh := mul_le_mul_of_nonneg_left hmul (mul_nonneg hsp.le hsN.le)
  ring_nf at hh ⊢
  simpa only [hsqN, hsqP, mul_comm, mul_left_comm, mul_assoc] using hh

end MajorityDynamics.GraphProcess.DayOne

