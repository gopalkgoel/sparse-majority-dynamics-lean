import MajorityDynamics.Idealized.LinearResponse.SparseRates
import MajorityDynamics.GraphProcess.LocalTransition.Algebra

noncomputable section
open Filter Topology
namespace MajorityDynamics.GraphProcess.FaithfulStep
open Idealized.LinearResponse Binomial.Approximation

/-- Both local fluctuations are absorbed uniformly in every next-day faithful scale. -/
theorem eventually_local_errors_sparse {θ T T1 C δ2 : ℝ}
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hT1 : 0 < T1) (hC : 0 ≤ C) (hδ : δ2 ≤ (1 - θ) / 8) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p → ∀ n : ℕ,
      C * LocalTransition.sizeScale N ≤
        T1 * Idealized.LinearResponse.sizeScale N p (n + 1) * (N : ℝ) ^ (-δ2) ∧
      C * LocalTransition.edgeScale N p ≤
        T1 * betaScale N p (n + 1) * (N : ℝ) ^ (-δ2) * (N : ℝ)^2 * p := by
  have hT0 : 0 < T := by linarith
  have ha : 0 < (1 - θ) / 4 - δ2 := by linarith
  have hcoef : 0 < T1 * T ^ (-(1:ℝ)/4) := by positivity
  filter_upwards [eventually_basic_sparse θ T hθlo hθhi hT,
    eventually_log_pow_le_rpow 1 ha (show 0 < T1 * T ^ (-(1:ℝ)/4) / (C+1) by positivity)]
    with N hb hl
  intro p hp n
  have hN : (0 : ℝ) < N := by exact_mod_cast hb.1
  have hp0 : 0 < (p : ℝ) := p.property.1
  have hx : 0 < (p : ℝ) * N := mul_pos p.property.1 hN
  have hs := (hb.2.2 p hp).1
  have hx1 : 1 ≤ (p : ℝ) * N := by nlinarith [Real.sq_sqrt hx.le]
  have hpow : (N : ℝ) ^ (1-θ) = (N : ℝ)^(-θ) * N := by
    rw [show 1-θ = -θ+1 by ring, Real.rpow_add_one hN.ne']
  have hlo : T⁻¹ * (N : ℝ) ^ (1-θ) ≤ (p : ℝ)*N := by
    rw [hpow, ← mul_assoc]
    exact (mul_lt_mul_of_pos_right hp.1 hN).le
  have hquarter : T ^ (-(1:ℝ)/4) * (N : ℝ)^((1-θ)/4) ≤
      ((p : ℝ)*N)^((1:ℝ)/4) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ T⁻¹ * (N : ℝ)^(1-θ)) hlo
      (by norm_num : 0 ≤ (1:ℝ)/4)
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hT0.le,
      ← Real.rpow_neg hT0.le, ← Real.rpow_mul hN.le] at h
    convert h using 1; congr 2 <;> ring
  have hlog : C * Real.log (N : ℝ) ≤
      T1 * ((p : ℝ)*N)^((1:ℝ)/4) * (N : ℝ)^(-δ2) := by
    have hratio : C * (T1 * T ^ (-(1:ℝ)/4) / (C+1)) ≤ T1 * T ^ (-(1:ℝ)/4) := by
      rw [← mul_div_assoc, div_le_iff₀ (show 0 < C+1 by positivity)]
      nlinarith
    calc
      C * Real.log (N : ℝ) ≤ C * (T1 * T ^ (-(1:ℝ)/4) / (C+1) *
          (N : ℝ)^((1-θ)/4-δ2)) := mul_le_mul_of_nonneg_left (by simpa using hl) hC
      _ ≤ T1 * T ^ (-(1:ℝ)/4) * (N : ℝ)^((1-θ)/4-δ2) := by
        simpa only [← mul_assoc] using mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hN.le _)
      _ = T1 * (T ^ (-(1:ℝ)/4) * (N : ℝ)^((1-θ)/4)) * (N : ℝ)^(-δ2) := by
        rw [show (1-θ)/4-δ2 = (1-θ)/4 + -δ2 by ring, Real.rpow_add hN]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hquarter hT1.le)
        (Real.rpow_nonneg hN.le _)
  have hnext : Real.sqrt ((p : ℝ)*N) ≤ Real.sqrt ((p : ℝ)*N)^(n+1) := by
    calc
      _ = 1 * Real.sqrt ((p : ℝ)*N) := by ring
      _ ≤ Real.sqrt ((p : ℝ)*N)^n * Real.sqrt ((p : ℝ)*N) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hs) (Real.sqrt_nonneg _)
      _ = _ := (pow_succ _ _).symm
  have hq : ((p : ℝ)*N)^((1:ℝ)/4) ≤ Real.sqrt ((p : ℝ)*N) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  constructor
  · have h := mul_le_mul_of_nonneg_left
      (hlog.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hq.trans hnext) hT1.le)
        (Real.rpow_nonneg hN.le _))) (Real.sqrt_nonneg (N : ℝ))
    simpa [LocalTransition.sizeScale, Idealized.LinearResponse.sizeScale, mul_assoc,
      mul_left_comm, mul_comm] using h
  · have he : ((p : ℝ)*N)^((1:ℝ)/14) * ((p : ℝ)*N)^((1:ℝ)/4) ≤
        Real.sqrt ((p : ℝ)*N) := by
      rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx.le ((1:ℝ)/14))
    have hh : C * (((p : ℝ)*N)^((1:ℝ)/14) * Real.log (N : ℝ)) ≤
        T1 * Real.sqrt ((p : ℝ)*N)^(n+1) * (N : ℝ)^(-δ2) := by
      calc
        _ ≤ T1 * (((p : ℝ)*N)^((1:ℝ)/14) * ((p : ℝ)*N)^((1:ℝ)/4)) *
            (N : ℝ)^(-δ2) := by nlinarith only [h]
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (he.trans hnext) hT1.le)
          (Real.rpow_nonneg hN.le _)
    have hf := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (N : ℝ)^2 * (p : ℝ) / Real.sqrt (N : ℝ) by positivity)
    rw [LocalTransition.edgeScale_eq N p hN p.property.1]
    simpa [LocalTransition.massScale, betaScale, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hf

/-- Any fixed positive density power absorbs one logarithm uniformly. -/
theorem eventually_log_le_pN_rpow_sparse {θ T a : ℝ}
    (hθhi : θ < 1) (hT : 0 < T) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      Real.log (N : ℝ) ≤ ((p : ℝ) * N)^a := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_log_pow_le_rpow 1 (mul_pos (sub_pos.mpr hθhi) ha)
      (show 0 < T^(-a) by positivity)] with N hN hl
  intro p hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : T⁻¹ * (N : ℝ)^(1-θ) ≤ (p : ℝ)*N := by
    rw [show 1-θ = -θ+1 by ring, Real.rpow_add_one hN0.ne', ← mul_assoc]
    exact (mul_lt_mul_of_pos_right hp.1 hN0).le
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ T⁻¹ * (N : ℝ)^(1-θ)) hlo ha.le
  rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hT.le,
    ← Real.rpow_neg hT.le, ← Real.rpow_mul hN0.le] at h
  exact (show Real.log (N : ℝ) ≤ T^(-a) * (N : ℝ)^((1-θ)*a) by simpa using hl).trans h

/-- Uniform scalar inequalities for the day-one concentration bounds. -/
theorem eventually_day_one_scales_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      Real.sqrt ((p : ℝ)*N) * Real.log (N : ℝ) ≤ ((p : ℝ)*N)^((4:ℝ)/7) ∧
      Real.sqrt ((p : ℝ)*N) * Real.log (N : ℝ) ≤ (p : ℝ)*N ∧
      (p : ℝ) ≤ Real.sqrt ((p : ℝ)*N) * Real.log (N : ℝ) / 2 ∧
      Real.sqrt ((N : ℝ)^2*p) * Real.log (N : ℝ) ≤ (N : ℝ)^2*p := by
  filter_upwards [eventually_basic_sparse θ T hθlo hθhi hT,
    eventually_log_le_pN_rpow_sparse hθhi (show 0 < T by linarith)
      (show 0 < (1:ℝ)/14 by norm_num)] with N hb hl
  intro p hp
  have hN : (0 : ℝ) < N := by exact_mod_cast hb.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hb.1
  have hp0 := p.property.1
  have hx : 0 < (p : ℝ)*N := mul_pos hp0 hN
  have hs := (hb.2.2 p hp).1
  have hx1 : 1 ≤ (p : ℝ)*N := by nlinarith [Real.sq_sqrt hx.le]
  have hl0 : 0 ≤ Real.log (N : ℝ) := by linarith [hb.2.1]
  have hlog : Real.log (N : ℝ) ≤ Real.sqrt ((p : ℝ)*N) := by
    calc
      _ ≤ ((p : ℝ)*N)^((1:ℝ)/14) := hl p hp
      _ ≤ _ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.sqrt ((p : ℝ)*N) * ((p : ℝ)*N)^((1:ℝ)/14) :=
        mul_le_mul_of_nonneg_left (hl p hp) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; norm_num
  · calc
      _ ≤ Real.sqrt ((p : ℝ)*N) * Real.sqrt ((p : ℝ)*N) :=
        mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hx.le
  · nlinarith [p.property.2, hb.2.1, mul_le_mul_of_nonneg_right hs hl0]
  · have hxy : (p : ℝ)*N ≤ (N : ℝ)^2*p := by
      nlinarith [mul_nonneg (show 0 ≤ (N : ℝ)-1 by linarith) hx.le]
    have hy : 0 ≤ (N : ℝ)^2*p := by positivity
    calc
      _ ≤ Real.sqrt ((N : ℝ)^2*p) * Real.sqrt ((N : ℝ)^2*p) :=
        mul_le_mul_of_nonneg_left (hlog.trans (Real.sqrt_le_sqrt hxy)) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hy
end MajorityDynamics.GraphProcess.FaithfulStep

