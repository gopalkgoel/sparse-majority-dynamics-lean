import MajorityDynamics.Binomial.ApproximationStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform scalar bounds in the A.2 density regime -/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Binomial.Approximation

theorem density_scale_lower (θ T K : ℝ) (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Probability, Density θ T n p →
      K * (Real.log n) ^ 3 ≤ scale n p := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := ((isLittleO_log_rpow_rpow_atTop 6 (by linarith : 0 < 1 - θ)).comp_tendsto
    hn).bound (show 0 < (T * K ^ 2)⁻¹ by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with n hn1 hbound
  intro p hp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hμ : 0 ≤ (p : ℝ) * n := mul_nonneg p.property.1.le hn0.le
  have hpow : (n : ℝ) ^ (1 - θ) = (n : ℝ) ^ (-θ) * n := by
    rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hn0.ne']
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hbound' : (Real.log n) ^ 6 ≤ (T * K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_ofNat,
      norm_pow, Real.norm_of_nonneg hlogpos,
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hbound
  have hd := mul_lt_mul_of_pos_right hp.1 hn0
  rw [mul_assoc, ← hpow] at hd
  have hsq : (K * (Real.log n) ^ 3) ^ 2 ≤ (p : ℝ) * n := by
    have hh := mul_le_mul_of_nonneg_left hbound' (sq_nonneg K)
    have heq : K ^ 2 * ((T * K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ)) =
        T⁻¹ * (n : ℝ) ^ (1 - θ) := by field_simp
    rw [heq] at hh
    nlinarith
  exact (Real.le_sqrt (by positivity) hμ).mpr hsq

theorem density_small_parameters (θ T : ℝ) (hθ : 1 / 2 < θ) (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Probability, Density θ T n p →
      (p : ℝ) ≤ 1 / 8 ∧ (p : ℝ) * scale n p ≤ 1 := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hup : Tendsto (fun n : ℕ => T * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < θ)).comp hn).const_mul T
  have hmid : Tendsto (fun n : ℕ => T * (n : ℝ) ^ (1 / 2 - θ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_sub, mul_zero] using
      ((tendsto_rpow_neg_atTop (show 0 < θ - 1 / 2 by linarith)).comp hn).const_mul T
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hup.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    hmid.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with n hn1 hu hm
  intro p hp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  refine ⟨(hp.2.trans hu).le, ?_⟩
  have hscale : scale n p ≤ Real.sqrt n := by
    apply Real.sqrt_le_sqrt
    exact (mul_le_mul_of_nonneg_right p.property.2.le hn0.le).trans_eq (one_mul _)
  calc
    (p : ℝ) * scale n p ≤ T * (n : ℝ) ^ (-θ) * Real.sqrt n :=
      mul_le_mul hp.2.le hscale (Real.sqrt_nonneg _) (by positivity)
    _ = T * (n : ℝ) ^ (1 / 2 - θ) := by
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hn0]
      congr 2
      ring
    _ ≤ 1 := hm.le

end MajorityDynamics.Binomial.Approximation
