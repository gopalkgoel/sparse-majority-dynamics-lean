import MajorityDynamics.Combinatorics.DegreeRatios.Basic
import MajorityDynamics.Binomial.DensityEstimates
import Mathlib.Tactic

noncomputable section
open Filter Topology

namespace MajorityDynamics.Combinatorics.DegreeRatios

def relativeConstant (T : ℝ) : ℝ := 4 * T ^ 2

def errorConstant (T : ℝ) : ℝ :=
  relativeConstant T + 4 * relativeConstant T ^ 2 + 120 * T + 10

/-- Sufficient numerical conditions, chosen before all integer inputs. -/
def LargeParameters (T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  64 * T ≤ (n : ℝ) ∧ 1 ≤ Real.log (n : ℝ) ∧
  0 < p ∧ p ≤ 1 / 16 ∧ (n : ℝ) * p ^ 2 ≤ 1 ∧
  2 * (relativeConstant T + 1) * (Real.log (n : ℝ) + 1) ≤ Real.sqrt (p * n)

/-- The threshold here depends only on `θ,T`, uniformly over real densities. -/
theorem eventually_large_parameters (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p → LargeParameters T n p := by
  have hT0 : 0 < T := by linarith
  have hK : 0 < relativeConstant T + 1 := by dsimp [relativeConstant]; positivity
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hup : Tendsto (fun n : ℕ => T * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < θ)).comp hn).const_mul T
  have hmid : Tendsto (fun n : ℕ => T * (n : ℝ) ^ (1 / 2 - θ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_sub, mul_zero] using
      ((tendsto_rpow_neg_atTop (by linarith : 0 < θ - 1 / 2)).comp hn).const_mul T
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp hn).eventually (eventually_ge_atTop 1)
  filter_upwards [hn.eventually (eventually_ge_atTop (64 * T)), hlog,
    eventually_ge_atTop (1 : ℕ),
    hup.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hmid.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    MajorityDynamics.Binomial.Approximation.density_scale_lower θ T
      (8 * (relativeConstant T + 1)) hθhi hT0 (by positivity)] with n hsize hlog hn1 hu hm hscale
  intro p hp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hp0 : 0 < p := (by positivity : 0 < T⁻¹ * (n : ℝ) ^ (-θ)).trans hp.1
  have hp16 : p ≤ 1 / 16 := (hp.2.trans hu).le
  let prob : MajorityDynamics.Binomial.Probability := ⟨p, hp0, by linarith⟩
  have hdensity : MajorityDynamics.Binomial.Approximation.Density θ T n prob := hp
  have hs := hscale prob hdensity
  change 8 * (relativeConstant T + 1) * Real.log (n : ℝ) ^ 3 ≤ Real.sqrt (p * n) at hs
  have hsparse : (n : ℝ) * p ^ 2 ≤ 1 := by
    have hsmall : p * Real.sqrt n ≤ 1 := by
      calc
        _ ≤ T * (n : ℝ) ^ (-θ) * Real.sqrt n :=
          mul_le_mul_of_nonneg_right hp.2.le (Real.sqrt_nonneg _)
        _ = T * (n : ℝ) ^ (1 / 2 - θ) := by
          rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hn0]
          congr 2
          ring
        _ ≤ 1 := hm.le
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ p * Real.sqrt n) zero_le_one).mpr hsmall
    rw [mul_pow, Real.sq_sqrt hn0.le, one_pow] at hh
    nlinarith
  refine ⟨hsize, hlog, hp0, hp16, hsparse, ?_⟩
  have hpow : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 3 := by
    have hh : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (n : ℝ) - 1)]
    have hm := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ Real.log (n : ℝ))
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hpow hK.le
  have hh1 := mul_le_mul_of_nonneg_left hlog hK.le
  nlinarith

end MajorityDynamics.Combinatorics.DegreeRatios
