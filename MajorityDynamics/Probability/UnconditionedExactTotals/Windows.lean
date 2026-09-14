import MajorityDynamics.Probability.UnconditionedExactTotals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.Probability.UnconditionedExactTotals

/-- Uniform size and probability control, chosen before any integer or tilt. -/
theorem eventually_windows {θ T : ℝ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ, DensityWindow θ T n p →
      0 < (n : ℝ) ∧ 0 < p ∧ p < 1 / 2 ∧
      (∀ a : ℤ, SizeWindow T n a → 1 ≤ a) ∧
      (∀ q : ℝ, TiltWindow T n p q → 0 < q ∧ q < 1 ∧ q < 2 * p) := by
  have hT0 : 0 < T := by linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ => T * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < θ)).comp hnat).const_mul T
  have hl : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - θ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hnat
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℕ)).and
      ((hu.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
        (hl.eventually_gt_atTop (4 * T ^ 3))))
  refine ⟨n₀, ?_⟩
  intro n hn p hp
  obtain ⟨hn1, hup, hlow⟩ := hn₀ n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < p := (mul_pos (inv_pos.mpr hT0) (Real.rpow_pos_of_pos hn0 _)).trans hp.1
  have hp1 : p < 1 / 2 := hp.2.trans hup
  have hpow : (n : ℝ) ^ (-θ) * n = (n : ℝ) ^ (1 - θ) := by
    calc
      _ = (n : ℝ) ^ (-θ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
  have hpn : 4 * T ^ 2 < p * n := by
    have hh := mul_lt_mul_of_pos_right hp.1 hn0
    have hh' := mul_lt_mul_of_pos_left hh hT0
    have heq : T * (T⁻¹ * (n : ℝ) ^ (-θ) * n) = (n : ℝ) ^ (1 - θ) := by
      rw [mul_assoc, ← mul_assoc T, mul_inv_cancel₀ hT0.ne', one_mul, hpow]
    rw [heq] at hh'
    nlinarith
  have hsqrt : 2 * T < Real.sqrt (p * n) := by
    have hs := Real.sq_sqrt (mul_pos hp0 hn0).le
    have hs0 := Real.sqrt_nonneg (p * n)
    nlinarith
  refine ⟨hn0, hp0, hp1, ?_, ?_⟩
  · intro a ha
    have ha0 : (0 : ℝ) < a := (mul_pos (inv_pos.mpr hT0) hn0).trans ha.1
    have : (0 : ℤ) < a := by exact_mod_cast ha0
    omega
  · intro q hq
    have hsq0 : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr (mul_pos hp0 hn0)
    have hdev : T * p / Real.sqrt (p * n) < p / 2 := by
      apply (div_lt_iff₀ hsq0).mpr
      nlinarith [mul_lt_mul_of_pos_right hsqrt hp0]
    exact ⟨by linarith [hq.1], by linarith [hq.2], by linarith [hq.2]⟩

/-- Integer centers are strictly interior; the upper comparison is uniform. -/
theorem center_bounds {d n : ℕ} {T p : ℝ} {m : ℤ} {η z : Fin d → ℤ} {q : Fin d → ℝ}
    (hT : 0 < T) (hn : 0 < (n : ℝ)) (_hp : 0 < p)
    (hm : 1 ≤ m) (hmw : SizeWindow T n m)
    (hη : ∀ t, 1 ≤ η t) (hηw : ∀ t, SizeWindow T n (η t))
    (hq : ∀ t, 0 < q t ∧ q t < 1 ∧ q t < 2 * p)
    (hz : ∀ t, (z t : ℝ) = (m : ℝ) * (η t : ℝ) * q t) (t : Fin d) :
    0 < z t ∧ z t < m * η t ∧ (z t : ℝ) ≤ (2 * T ^ 2) * ((n : ℝ) ^ 2 * p) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have he0 : 0 < (η t : ℝ) := by exact_mod_cast (show 0 < η t by have := hη t; omega)
  have hz0 : (0 : ℝ) < z t := by rw [hz]; exact mul_pos (mul_pos hm0 he0) (hq t).1
  have hzlt : (z t : ℝ) < (m : ℝ) * (η t : ℝ) := by
    rw [hz]
    exact mul_lt_of_lt_one_right (mul_pos hm0 he0) (hq t).2.1
  refine ⟨by exact_mod_cast hz0, by exact_mod_cast hzlt, ?_⟩
  have hme := mul_le_mul hmw.2.le (hηw t).2.le he0.le (mul_pos hT hn).le
  have hh := mul_le_mul hme (hq t).2.2.le (hq t).1.le (by positivity : 0 ≤ T * n * (T * n))
  rw [hz]
  nlinarith

end MajorityDynamics.Probability.UnconditionedExactTotals
